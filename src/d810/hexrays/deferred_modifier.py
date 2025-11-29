"""
Deferred Graph Modifier for Microcode CFG Changes

This module provides a queue-based system for deferring CFG modifications
until all analysis is complete. This prevents issues that occur when
modifying the graph during iteration.

Based on the pattern described by hex-rays plugin developers:
- Queue all graph modifications during analysis
- Apply them in a controlled order after analysis completes
- Handle instruction removals last to preserve tracking information

Supported modification types:
- block_target_change: Change a conditional jump's target
- block_fallthrough_change: Change a block's fallthrough successor
- block_goto_change: Change an unconditional goto's destination
- block_nop_insns: NOP specific instructions in a block
- block_convert_to_goto: Convert a 2-way block to a 1-way goto
- insn_remove: Remove a specific instruction (deferred until end)
"""
from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum, auto
from typing import TYPE_CHECKING

import ida_hexrays

from d810.core import getLogger
from d810.hexrays.cfg_utils import (
    change_1way_block_successor,
    change_2way_block_conditional_successor,
    make_2way_block_goto,
    mba_deep_cleaning,
    safe_verify,
)

if TYPE_CHECKING:
    pass

logger = getLogger("D810.deferred_modifier")


class ModificationType(Enum):
    """Types of graph modifications that can be queued."""
    BLOCK_GOTO_CHANGE = auto()       # Change goto destination
    BLOCK_TARGET_CHANGE = auto()      # Change conditional jump target
    BLOCK_FALLTHROUGH_CHANGE = auto() # Change fallthrough successor
    BLOCK_CONVERT_TO_GOTO = auto()    # Convert 2-way to 1-way block
    BLOCK_NOP_INSNS = auto()          # NOP instructions in a block
    INSN_REMOVE = auto()              # Remove a specific instruction
    INSN_NOP = auto()                 # NOP a specific instruction


@dataclass
class GraphModification:
    """Represents a single queued graph modification."""
    mod_type: ModificationType
    block_serial: int
    # Target for goto/jump changes
    new_target: int | None = None
    # For instruction-level operations
    insn_ea: int | None = None
    # Priority for ordering (lower = earlier)
    priority: int = 100
    # Description for logging
    description: str = ""


@dataclass
class DeferredGraphModifier:
    """
    Queue-based graph modifier that defers all changes until apply() is called.

    Usage:
        modifier = DeferredGraphModifier(mba)

        # Queue modifications during analysis
        modifier.queue_goto_change(block_serial=10, new_target=20)
        modifier.queue_convert_to_goto(block_serial=15, goto_target=25)
        modifier.queue_insn_remove(block_serial=10, insn_ea=0x1234)

        # Apply all modifications at once
        changes = modifier.apply()
    """
    mba: ida_hexrays.mba_t
    modifications: list[GraphModification] = field(default_factory=list)
    _applied: bool = False

    def reset(self) -> None:
        """Clear all queued modifications."""
        self.modifications.clear()
        self._applied = False

    def queue_goto_change(
        self,
        block_serial: int,
        new_target: int,
        description: str = "",
    ) -> None:
        """Queue a change to an unconditional goto's destination."""
        self.modifications.append(GraphModification(
            mod_type=ModificationType.BLOCK_GOTO_CHANGE,
            block_serial=block_serial,
            new_target=new_target,
            priority=10,  # High priority - do block changes first
            description=description or f"goto {block_serial} -> {new_target}",
        ))
        logger.debug("Queued goto change: block %d -> %d", block_serial, new_target)

    def queue_conditional_target_change(
        self,
        block_serial: int,
        new_target: int,
        description: str = "",
    ) -> None:
        """Queue a change to a conditional jump's target."""
        self.modifications.append(GraphModification(
            mod_type=ModificationType.BLOCK_TARGET_CHANGE,
            block_serial=block_serial,
            new_target=new_target,
            priority=10,
            description=description or f"jmp target {block_serial} -> {new_target}",
        ))
        logger.debug("Queued target change: block %d -> %d", block_serial, new_target)

    def queue_convert_to_goto(
        self,
        block_serial: int,
        goto_target: int,
        description: str = "",
    ) -> None:
        """Queue conversion of a 2-way block to a 1-way goto."""
        self.modifications.append(GraphModification(
            mod_type=ModificationType.BLOCK_CONVERT_TO_GOTO,
            block_serial=block_serial,
            new_target=goto_target,
            priority=20,  # After simple target changes
            description=description or f"convert {block_serial} to goto {goto_target}",
        ))
        logger.debug("Queued convert to goto: block %d -> %d", block_serial, goto_target)

    def queue_insn_remove(
        self,
        block_serial: int,
        insn_ea: int,
        description: str = "",
    ) -> None:
        """Queue removal of a specific instruction (by EA)."""
        self.modifications.append(GraphModification(
            mod_type=ModificationType.INSN_REMOVE,
            block_serial=block_serial,
            insn_ea=insn_ea,
            priority=1000,  # Very low priority - do last
            description=description or f"remove insn at {hex(insn_ea)} in block {block_serial}",
        ))
        logger.debug("Queued insn remove: block %d, ea=%s", block_serial, hex(insn_ea))

    def queue_insn_nop(
        self,
        block_serial: int,
        insn_ea: int,
        description: str = "",
    ) -> None:
        """Queue NOP of a specific instruction (by EA)."""
        self.modifications.append(GraphModification(
            mod_type=ModificationType.INSN_NOP,
            block_serial=block_serial,
            insn_ea=insn_ea,
            priority=900,  # Low priority but before removes
            description=description or f"nop insn at {hex(insn_ea)} in block {block_serial}",
        ))
        logger.debug("Queued insn nop: block %d, ea=%s", block_serial, hex(insn_ea))

    def has_modifications(self) -> bool:
        """Check if there are any queued modifications."""
        return len(self.modifications) > 0

    def apply(
        self,
        run_optimize_local: bool = True,
        run_deep_cleaning: bool = False,
    ) -> int:
        """
        Apply all queued modifications in priority order.

        Args:
            run_optimize_local: If True, call mba.optimize_local(0) after changes
            run_deep_cleaning: If True, run mba_deep_cleaning after changes

        Returns:
            Number of successful modifications applied.
        """
        if self._applied:
            logger.warning("DeferredGraphModifier.apply() called twice")
            return 0

        if not self.modifications:
            logger.debug("No modifications to apply")
            return 0

        # Sort by priority (lower = earlier)
        sorted_mods = sorted(self.modifications, key=lambda m: m.priority)

        logger.info("Applying %d queued graph modifications", len(sorted_mods))

        successful = 0
        failed = 0

        for mod in sorted_mods:
            try:
                if self._apply_single(mod):
                    successful += 1
                    logger.debug("Applied: %s", mod.description)
                else:
                    failed += 1
                    logger.warning("Failed to apply: %s", mod.description)
            except Exception as e:
                failed += 1
                logger.error("Exception applying %s: %s", mod.description, e)

        logger.info(
            "Applied %d/%d modifications (%d failed)",
            successful, len(sorted_mods), failed
        )

        # Mark chains dirty and run optimizations
        if successful > 0:
            self.mba.mark_chains_dirty()

            if run_deep_cleaning:
                mba_deep_cleaning(self.mba, call_mba_combine_block=True)
            elif run_optimize_local:
                self.mba.optimize_local(0)

            safe_verify(
                self.mba,
                "after deferred modifications",
                logger_func=logger.error,
            )

        self._applied = True
        return successful

    def _apply_single(self, mod: GraphModification) -> bool:
        """Apply a single modification. Returns True on success."""
        blk = self.mba.get_mblock(mod.block_serial)
        if blk is None:
            logger.warning("Block %d not found", mod.block_serial)
            return False

        if mod.mod_type == ModificationType.BLOCK_GOTO_CHANGE:
            return self._apply_goto_change(blk, mod.new_target)

        elif mod.mod_type == ModificationType.BLOCK_TARGET_CHANGE:
            return self._apply_target_change(blk, mod.new_target)

        elif mod.mod_type == ModificationType.BLOCK_CONVERT_TO_GOTO:
            return self._apply_convert_to_goto(blk, mod.new_target)

        elif mod.mod_type == ModificationType.INSN_REMOVE:
            return self._apply_insn_remove(blk, mod.insn_ea)

        elif mod.mod_type == ModificationType.INSN_NOP:
            return self._apply_insn_nop(blk, mod.insn_ea)

        else:
            logger.warning("Unknown modification type: %s", mod.mod_type)
            return False

    def _apply_goto_change(self, blk: ida_hexrays.mblock_t, new_target: int) -> bool:
        """Change an unconditional goto's destination."""
        if blk.tail is None or blk.tail.opcode != ida_hexrays.m_goto:
            logger.warning(
                "Block %d doesn't end with goto (opcode=%s)",
                blk.serial,
                blk.tail.opcode if blk.tail else "none"
            )
            return False

        return change_1way_block_successor(blk, new_target)

    def _apply_target_change(self, blk: ida_hexrays.mblock_t, new_target: int) -> bool:
        """Change a conditional jump's target."""
        if blk.tail is None:
            return False

        # Check if it's a conditional jump
        if blk.tail.opcode not in [
            ida_hexrays.m_jnz, ida_hexrays.m_jz,
            ida_hexrays.m_jae, ida_hexrays.m_jb,
            ida_hexrays.m_ja, ida_hexrays.m_jbe,
            ida_hexrays.m_jg, ida_hexrays.m_jge,
            ida_hexrays.m_jl, ida_hexrays.m_jle,
        ]:
            logger.warning(
                "Block %d doesn't end with conditional jump",
                blk.serial
            )
            return False

        return change_2way_block_conditional_successor(blk, new_target)

    def _apply_convert_to_goto(self, blk: ida_hexrays.mblock_t, goto_target: int) -> bool:
        """Convert a 2-way block to a 1-way goto."""
        return make_2way_block_goto(blk, goto_target)

    def _apply_insn_remove(self, blk: ida_hexrays.mblock_t, insn_ea: int) -> bool:
        """Remove an instruction by its EA."""
        insn = blk.head
        while insn:
            if insn.ea == insn_ea:
                blk.remove_from_block(insn)
                return True
            insn = insn.next

        logger.warning(
            "Instruction at EA %s not found in block %d",
            hex(insn_ea), blk.serial
        )
        return False

    def _apply_insn_nop(self, blk: ida_hexrays.mblock_t, insn_ea: int) -> bool:
        """NOP an instruction by its EA."""
        insn = blk.head
        while insn:
            if insn.ea == insn_ea:
                blk.make_nop(insn)
                return True
            insn = insn.next

        logger.warning(
            "Instruction at EA %s not found in block %d",
            hex(insn_ea), blk.serial
        )
        return False
