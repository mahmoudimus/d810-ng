"""
Unflattener for Bad While Loop
TODO:

# - Accept m_jz and m_jnz (plus support for == or != with non-zero constants).
# - Allow the state register to be either l or r operand (code should not assume only l).
# - Add an optional alias check: for example, if there is 'mov eax, tmp', look back for an earlier 'mov tmp, #CONST'.
# - If possible, do not rely only on prevb/nextb; make sure selected exits are actual successors using the CFG (succset) to avoid incorrect matches after layout changes.
# - Keep 'min_constant' and 'max_constant' as configuration options; these are important to filter out irrelevant matches.

"""

from ida_hexrays import *

from d810.core import getLogger
from d810.hexrays.hexrays_helpers import append_mop_if_not_in_list
from d810.optimizers.microcode.flow.flattening.generic import (
    GenericDispatcherBlockInfo,
    GenericDispatcherCollector,
    GenericDispatcherInfo,
    GenericDispatcherUnflatteningRule,
)

unflat_logger = getLogger(__name__)
FLATTENING_JUMP_OPCODES = [m_jz]


class BadWhileLoopBlockInfo(GenericDispatcherBlockInfo):
    pass


class BadWhileLoopInfo(GenericDispatcherInfo):
    def explore(self, blk: mblock_t, min_constant=None, max_constant=None) -> bool:
        """
        ; 1WAY-BLOCK 13 [START=0000E1BE END=0000E1D0] STK=48/ARG=250, MAXBSP: 0
        ; - INBOUND: [12, 24, 25, 8] OUTBOUND: [14]
        13. 0 mov    #0xF6A1F.4, eax.4                    ; 0000E1BE
        goto 16

        ; 2WAY-BLOCK 14 [START=0000E1D0 END=0000E1DB] STK=48/ARG=250, MAXBSP: 0
        ; - INBOUND: [13, 18] OUTBOUND: [15, 21]
        14. 0 jz     eax.4, #0xF6A1E.4, @21               ; 0000E1D5

        ; 2WAY-BLOCK 15 [START=0000E1DB END=0000E1E2] STK=48/ARG=250, MAXBSP: 0
        ; - INBOUND: [14] OUTBOUND: [16, 19]
        15. 0 jz     eax.4, #0xF6A20.4, @19

        ; 2WAY-BLOCK 16 [START=0000E204 END=0000E213] STK=48/ARG=250, MAXBSP: 0
        ; - INBOUND: [15] OUTBOUND: [17, 26]
        16. 0 mov    #0xF6A25.8, rcx.8                    ; 0000E21F
        16. 1 jz     [ds.2:r12.8].1, #0.1, @26

        17. 0 mov    #0xF6A1E.4, eax.4

        18. 0 mov    #0.8, rdx.8{18}                      ; 0000E0FD
        18. 1 goto   @21

        ; - INBOUND: [16] OUTBOUND: [18]
        26. 0 mov    #0xF6A20.4, eax.4                    ; 0000E218
        26. 1 goto   @19


        entry_block = 14
        exit_blocks = 21 & 16 & 19


        """
        # Use provided values or defaults (Approov obfuscator range)
        if min_constant is None:
            min_constant = 0xF6000
        if max_constant is None:
            max_constant = 0xF6FFF

        self.reset()
        if not self._is_candidate_for_dispatcher_entry_block(
            blk, min_constant, max_constant
        ):
            return False
        self.entry_block = BadWhileLoopBlockInfo(blk)
        self.mop_compared = blk.tail.l
        self.entry_block.parse()
        for used_mop in self.entry_block.use_list:
            append_mop_if_not_in_list(used_mop, self.entry_block.assume_def_list)
        self.dispatcher_internal_blocks.append(self.entry_block)
        if (
            blk.tail.opcode == m_jz
            and blk.tail.r.t == mop_n
            and blk.nextb != None
            and blk.prevb != None
        ):
            right_cnst = blk.tail.r.signed_value()
            if right_cnst > min_constant and right_cnst < max_constant:
                if blk.prevb.tail.opcode == m_mov and blk.prevb.tail.l.t == mop_n:
                    jz0_cnst = blk.prevb.tail.l.signed_value()
                    if blk.nextb.tail.opcode == m_jz and blk.nextb.tail.r.t == mop_n:
                        jz1_cnst = blk.nextb.tail.r.signed_value()
                        if (
                            jz1_cnst > min_constant
                            and jz1_cnst < max_constant
                            and jz0_cnst > min_constant
                            and jz0_cnst < max_constant
                        ):
                            exit_block0 = BadWhileLoopBlockInfo(
                                blk.mba.get_mblock(blk.nextb.tail.d.b), self.entry_block
                            )
                            self.dispatcher_exit_blocks.append(exit_block0)
                            self.comparison_values.append(jz1_cnst)
                            exit_block1 = BadWhileLoopBlockInfo(
                                blk.mba.get_mblock(blk.nextb.nextb.serial),
                                self.entry_block,
                            )
                            self.dispatcher_exit_blocks.append(exit_block1)
                            self.comparison_values.append(right_cnst)
                            exit_block2 = BadWhileLoopBlockInfo(
                                blk.mba.get_mblock(blk.prevb.serial), self.entry_block
                            )
                            self.dispatcher_exit_blocks.append(exit_block2)
                            self.comparison_values.append(jz0_cnst)

        return True

    def _is_candidate_for_dispatcher_entry_block(self, blk, min_constant, max_constant):
        if (
            blk.tail.opcode == m_jz
            and blk.tail.r.t == mop_n
            and blk.nextb != None
            and blk.prevb != None
        ):
            right_cnst = blk.tail.r.signed_value()
            if right_cnst > min_constant and right_cnst < max_constant:
                if blk.prevb.tail.opcode == m_mov and blk.prevb.tail.l.t == mop_n:
                    jz0_cnst = blk.prevb.tail.l.signed_value()
                    if blk.nextb.tail.opcode == m_jz and blk.nextb.tail.r.t == mop_n:
                        jz1_cnst = blk.nextb.tail.r.signed_value()
                        if (
                            jz1_cnst > min_constant
                            and jz1_cnst < max_constant
                            and jz0_cnst > min_constant
                            and jz0_cnst < max_constant
                        ):
                            return True
        return False

    def _get_comparison_info(self, blk: mblock_t):
        # blk.tail must be a jtbl
        if (blk.tail is None) or (blk.tail.opcode != m_jtbl):
            return None, None
        return blk.tail.l, blk.tail.r


class BadWhileLoopCollector(GenericDispatcherCollector):
    DISPATCHER_CLASS = BadWhileLoopInfo
    DEFAULT_DISPATCHER_MIN_INTERNAL_BLOCK = 1
    DEFAULT_DISPATCHER_MIN_EXIT_BLOCK = 3
    DEFAULT_DISPATCHER_MIN_COMPARISON_VALUE = 3
    DEFAULT_MIN_CONSTANT = 0xF6000
    DEFAULT_MAX_CONSTANT = 0xF6FFF

    def __init__(self):
        super().__init__()
        self.min_constant = self.DEFAULT_MIN_CONSTANT
        self.max_constant = self.DEFAULT_MAX_CONSTANT

    def configure(self, kwargs):
        super().configure(kwargs)
        if "min_constant" in kwargs:
            self.min_constant = kwargs["min_constant"]
            unflat_logger.debug(
                "BadWhileLoopCollector: min_constant set to 0x%X", self.min_constant
            )
        if "max_constant" in kwargs:
            self.max_constant = kwargs["max_constant"]
            unflat_logger.debug(
                "BadWhileLoopCollector: max_constant set to 0x%X", self.max_constant
            )

    def visit_minsn(self):
        """Override to pass min/max constant parameters to explore."""

        if self.blk.serial in self.explored_blk_serials:
            return 0
        self.explored_blk_serials.append(self.blk.serial)
        if self.curins.opcode not in FLATTENING_JUMP_OPCODES:
            return 0
        disp_info = self.DISPATCHER_CLASS(self.blk.mba)

        # Pass constants as kwargs
        kwargs = {}
        if hasattr(self, "min_constant"):
            kwargs["min_constant"] = self.min_constant
        if hasattr(self, "max_constant"):
            kwargs["max_constant"] = self.max_constant

        is_good_candidate = disp_info.explore(self.blk, **kwargs)
        if not is_good_candidate:
            return 0
        if not self.specific_checks(disp_info):
            return 0
        self.dispatcher_list.append(disp_info)
        return 0


class BadWhileLoop(GenericDispatcherUnflatteningRule):
    DESCRIPTION = "Remove control flow flattening generated by approov"
    DEFAULT_UNFLATTENING_MATURITIES = [MMAT_GLBOPT1]
    DEFAULT_MAX_DUPLICATION_PASSES = 20
    DEFAULT_MAX_PASSES = 5

    @property
    def DISPATCHER_COLLECTOR_CLASS(self) -> type[GenericDispatcherCollector]:
        """Return the class of the dispatcher collector."""
        return BadWhileLoopCollector



"""
# BadWhileLoop recognizes a very specific "Approov-style" dispatcher head by looking for:
#   - a jz on a magic constant,
#   - a previous mov #magic, eax,
#   - a next jz on another magic constant,
# and then it collects 3 exits from (next jz target, next fall-through, previous block).
# The generic unflattening framework then uses those to rewire the CFG and remove the flattened while loop.
"""
