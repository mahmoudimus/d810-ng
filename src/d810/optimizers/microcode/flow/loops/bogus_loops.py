"""
Bogus Single-Iteration Loop Removal

This handler detects and removes obfuscation loops that are designed to execute
exactly once. The pattern is:

    for (i = 0; !i; i = 1) {
        // body
    }

Which in microcode becomes:
    1. Initialize counter to constant C1 (e.g., 0)
    2. Check if counter != C1, if so exit loop
    3. Execute loop body
    4. Set counter to different constant C2 (e.g., 1)
    5. Jump back to check

This always executes exactly once and can be safely unrolled.
"""

from ida_hexrays import *

from d810.core import getLogger
from d810.hexrays.cfg_utils import (
    change_1way_block_successor,
    make_2way_block_goto,
    mba_deep_cleaning,
)
from d810.hexrays.hexrays_helpers import CONDITIONAL_JUMP_OPCODES
from d810.optimizers.microcode.flow.handler import FlowOptimizationRule

logger = getLogger("D810.bogus_loop_remover")


class BogusLoopInfo:
    """Information about a detected bogus single-iteration loop."""

    def __init__(self):
        self.init_block = None  # Block that initializes the counter
        self.check_block = None  # Block that checks the counter
        self.body_blocks = []  # Blocks in the loop body
        self.exit_block = None  # Block after the loop exits
        self.counter_var = None  # The loop counter variable (mop_t)
        self.init_value = None  # Initial value of counter
        self.increment_value = None  # Value counter is set to at end
        self.is_valid = False


def get_mop_from_stack_var(mop: mop_t) -> tuple[int, int] | None:
    """Extract (offset, size) from a stack variable mop."""
    if mop.t == mop_S:
        return (mop.s.off, mop.size)
    return None


def mops_equal(mop1: mop_t, mop2: mop_t) -> bool:
    """Check if two mops refer to the same location."""
    if mop1 is None or mop2 is None:
        return False

    # For stack variables
    if mop1.t == mop_S and mop2.t == mop_S:
        return mop1.s.off == mop2.s.off and mop1.size == mop2.size

    # For registers
    if mop1.t == mop_r and mop2.t == mop_r:
        return mop1.r == mop2.r and mop1.size == mop2.size

    return False


def is_simple_constant_assignment(ins: minsn_t) -> tuple[mop_t | None, int | None]:
    """
    Check if instruction is a simple assignment of a constant to a variable.
    Returns (destination_mop, constant_value) or (None, None).
    """
    if ins is None or ins.opcode != m_mov:
        return None, None

    # Check if right side is a constant
    if ins.l.t != mop_n:
        return None, None

    # Check if destination is a stack variable or register
    if ins.d.t not in [mop_S, mop_r]:
        return None, None

    return ins.d, ins.l.nnn.value


def find_counter_increment_in_block(blk: mblock_t, counter_var: mop_t) -> int | None:
    """
    Look for an instruction that sets the counter variable to a constant.
    Returns the constant value or None.
    """
    cur_ins = blk.head
    while cur_ins is not None:
        dst, const_val = is_simple_constant_assignment(cur_ins)
        if dst is not None and mops_equal(dst, counter_var):
            return const_val
        cur_ins = cur_ins.next
    return None


def analyze_bogus_loop(blk: mblock_t) -> BogusLoopInfo:
    """
    Analyze a block to see if it's part of a bogus single-iteration loop.

    Pattern to detect:
    1. Current block (check_block) has conditional jump checking counter != init_value
    2. Loop body sets counter to different value
    3. Body jumps back to check_block

    Example microcode pattern:
        Block N:   mov #0, %var_counter      ; init
        Block N+1: jnz %var_counter, #0, @exit  ; check (this block)
        Block N+2: <body>                    ; body starts
        Block N+3: mov #1, %var_counter      ; set to different value
                   goto @N+1                 ; back edge
        Block exit: ...                      ; post-loop
    """
    info = BogusLoopInfo()

    # Must be a 2-way block (conditional jump)
    if blk.nsucc() != 2:
        return info

    if blk.tail is None or blk.tail.opcode not in CONDITIONAL_JUMP_OPCODES:
        return info

    info.check_block = blk

    # Analyze the conditional jump
    # Looking for patterns like: jnz %var_1C.4, #0.4, @exit_block
    # or: jz %var_1C.4, #0.4, @body_block

    jump_ins = blk.tail
    left_mop = jump_ins.l
    right_mop = jump_ins.r

    # One operand must be a constant (the comparison value)
    # The other must be a variable (the counter)
    counter_var = None
    compare_value = None

    if left_mop.t == mop_n and right_mop.t in [mop_S, mop_r]:
        compare_value = left_mop.nnn.value
        counter_var = right_mop
    elif right_mop.t == mop_n and left_mop.t in [mop_S, mop_r]:
        compare_value = right_mop.nnn.value
        counter_var = left_mop
    else:
        return info

    info.counter_var = counter_var
    info.init_value = compare_value

    # Determine which successor is the exit and which is the body
    conditional_succ_serial = jump_ins.d.b
    direct_succ_serial = blk.serial + 1

    # For jnz %var, #0:
    #   - If var == 0 (initially), condition is false, takes direct successor (fallthrough)
    #   - If var != 0 (after loop), condition is true, takes conditional successor (jump target)
    # So: direct_succ is body, conditional_succ is exit
    #
    # For jz %var, #0:
    #   - If var == 0 (initially), condition is true, takes conditional successor (jump target)
    #   - If var != 0 (after loop), condition is false, takes direct successor (fallthrough)
    # So: conditional_succ is body, direct_succ is exit

    if jump_ins.opcode == m_jnz:
        # jnz: jumps when condition is true (!=)
        # Initially counter == compare_value, so doesn't jump → body is fallthrough
        body_serial = direct_succ_serial
        exit_serial = conditional_succ_serial
    elif jump_ins.opcode == m_jz:
        # jz: jumps when condition is true (==)
        # Initially counter == compare_value, so jumps → body is jump target
        body_serial = conditional_succ_serial
        exit_serial = direct_succ_serial
    else:
        # Other conditional jumps - could extend for jae, jb, etc.
        return info

    mba = blk.mba

    # Validate that successors exist
    if body_serial >= mba.qty or exit_serial >= mba.qty:
        return info

    body_block = mba.get_mblock(body_serial)
    exit_block = mba.get_mblock(exit_serial)

    # Now trace through the body to find where counter is set and where it loops back
    visited = set()
    current = body_block
    body_blocks = []

    # Follow the body blocks until we find one that:
    # 1. Sets the counter to a different value
    # 2. Jumps back to check_block

    max_depth = 10  # Prevent infinite loops
    depth = 0
    found_increment = False
    increment_value = None

    while current and depth < max_depth:
        if current.serial in visited:
            break
        visited.add(current.serial)
        body_blocks.append(current)
        depth += 1

        # Look for counter increment in this block
        inc_val = find_counter_increment_in_block(current, counter_var)
        if inc_val is not None and inc_val != compare_value:
            found_increment = True
            increment_value = inc_val

        # Check successors
        if current.nsucc() == 1:
            next_serial = current.succset[0]
            if next_serial == blk.serial:
                # Found the back edge to check block!
                if found_increment:
                    info.body_blocks = body_blocks
                    info.exit_block = exit_block
                    info.increment_value = increment_value
                    info.is_valid = True
                break
            # Continue to next block in body
            if next_serial < mba.qty:
                current = mba.get_mblock(next_serial)
            else:
                break
        elif current.nsucc() == 0:
            # End of body without looping back
            break
        else:
            # Body has conditional jump - more complex pattern
            # For now, we don't handle this
            break

    return info


class BogusLoopRemover(FlowOptimizationRule):
    """
    Removes bogus single-iteration loops used for obfuscation.

    These loops have the pattern:
        for (i = C1; i == C1; i = C2) { body }

    Which always executes exactly once and can be safely unrolled.
    """

    def __init__(self):
        super().__init__()
        self.nb_changes = 0

    def optimize(self, blk: mblock_t) -> int:
        """
        Analyze and optimize the given block.

        Returns the number of changes made.
        """
        info = analyze_bogus_loop(blk)

        if not info.is_valid:
            return 0

        logger.info(
            "Found bogus single-iteration loop at block %d (counter: init=%d, inc=%d)",
            info.check_block.serial,
            info.init_value,
            info.increment_value,
        )

        # Remove the loop by:
        # 1. Change check_block to jump directly to first body block (remove the conditional)
        # 2. Change last body block to jump to exit_block instead of back to check_block

        mba = blk.mba

        # Find the first body block (it's the one that the check block should enter)
        if len(info.body_blocks) == 0:
            logger.warning(
                "No body blocks found for bogus loop at block %d", blk.serial
            )
            return 0

        first_body_serial = info.body_blocks[0].serial
        exit_serial = info.exit_block.serial

        # Change the check block from conditional jump to unconditional goto to body
        logger.info(
            "  Changing block %d from conditional to goto %d (body)",
            info.check_block.serial,
            first_body_serial,
        )
        make_2way_block_goto(info.check_block, first_body_serial)

        # Change the last body block to jump to exit instead of looping back
        last_body_block = info.body_blocks[-1]
        if (
            last_body_block.nsucc() == 1
            and last_body_block.succset[0] == info.check_block.serial
        ):
            logger.info(
                "  Changing block %d to goto %d (exit) instead of %d (check)",
                last_body_block.serial,
                exit_serial,
                info.check_block.serial,
            )
            change_1way_block_successor(last_body_block, exit_serial)

        # Clean up the graph
        mba_deep_cleaning(mba, call_mba_combine_block=True)

        self.nb_changes += 1
        return 1
