"""Composable services for control-flow flattening removal.

This module decomposes the monolithic GenericDispatcherUnflatteningRule into
smaller, single-responsibility services that can be composed together.

Following the composition-over-inheritance principle, these services are:
- Easier to test in isolation
- Easier to understand (each does one thing)
- Easier to reuse in different contexts
- Easier to modify without breaking other functionality
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import List, Protocol, Tuple

import ida_hexrays

from d810.optimizers.core import OptimizationContext


@dataclass(frozen=True)
class Dispatcher:
    """Structured data representing a discovered control-flow flattening dispatcher.

    This immutable dataclass replaces the mutable GenericDispatcherInfo class,
    making dispatcher information explicit and easier to work with.

    A dispatcher is the central switch/dispatch block in a control-flow
    flattening obfuscation. It reads a state variable and jumps to different
    blocks based on that value.

    Attributes:
        entry_block: The microcode block that serves as the dispatcher entry.
        state_variable: The mop (microcode operand) used for dispatching decisions.
        comparison_values: List of constant values the state variable is compared against.
        internal_blocks: Blocks that are part of the dispatcher's internal logic.
        exit_blocks: Blocks that the dispatcher can transfer control to.
        mba: The microcode array containing this dispatcher.
    """
    entry_block: ida_hexrays.mblock_t
    state_variable: ida_hexrays.mop_t
    comparison_values: List[int] = field(default_factory=list)
    internal_blocks: List[ida_hexrays.mblock_t] = field(default_factory=list)
    exit_blocks: List[ida_hexrays.mblock_t] = field(default_factory=list)
    mba: ida_hexrays.mba_t | None = None

    def __str__(self) -> str:
        """Return a human-readable representation of this dispatcher."""
        return (
            f"Dispatcher(entry={self.entry_block.serial}, "
            f"state_var={self.state_variable}, "
            f"values={len(self.comparison_values)}, "
            f"exits={len(self.exit_blocks)})"
        )


class DispatcherFinder(Protocol):
    """Protocol for services that find dispatchers in microcode.

    Different obfuscation schemes (O-LLVM, Tigress, etc.) use different
    dispatcher patterns. By defining this as a protocol, we can have
    multiple implementations without coupling to a specific pattern.

    Example implementations:
    - OLLVMDispatcherFinder: Finds O-LLVM style dispatchers
    - TigressDispatcherFinder: Finds Tigress style dispatchers
    - HeuristicDispatcherFinder: Uses heuristics for unknown obfuscators
    """

    def find(self, context: OptimizationContext) -> List[Dispatcher]:
        """Find all dispatchers in the given microcode.

        This method analyzes the control flow graph to identify blocks
        that act as dispatchers in a control-flow flattening scheme.

        Args:
            context: The optimization context containing the mba and configuration.

        Returns:
            A list of Dispatcher objects representing found dispatchers.
            Empty list if no dispatchers are found.

        Example:
            >>> finder = OLLVMDispatcherFinder()
            >>> dispatchers = finder.find(context)
            >>> for dispatcher in dispatchers:
            ...     print(f"Found dispatcher at block {dispatcher.entry_block.serial}")
        """
        ...


class PathEmulator:
    """Emulates microcode execution paths to resolve state variables.

    This service wraps the complex MopTracker and MicroCodeInterpreter logic
    into a simple, testable interface. It's responsible for determining what
    value a state variable will have when reaching a dispatcher.

    The emulation is key to unflattening: we need to know which dispatcher
    exit block will be taken for each predecessor block.

    Example:
        >>> emulator = PathEmulator()
        >>> target = emulator.resolve_target(context, pred_block, dispatcher)
        >>> print(f"Block {pred_block.serial} will jump to {target.serial}")
    """

    def resolve_target(
        self,
        context: OptimizationContext,
        from_block: ida_hexrays.mblock_t,
        dispatcher: Dispatcher
    ) -> ida_hexrays.mblock_t | None:
        """Emulate execution from from_block through the dispatcher.

        This method:
        1. Tracks the dispatcher's state variable backwards from from_block
        2. Determines its constant value (if resolvable)
        3. Emulates the dispatcher logic with that value
        4. Returns the actual target block (bypassing the dispatcher)

        Args:
            context: The optimization context.
            from_block: The predecessor block jumping to the dispatcher.
            dispatcher: The dispatcher to emulate through.

        Returns:
            The actual target block that from_block should jump to directly.
            None if the target cannot be resolved (e.g., state variable depends on input).

        Raises:
            ValueError: If emulation fails unexpectedly.

        Example:
            >>> # Before: block_5 -> dispatcher -> block_42
            >>> # After:  block_5 -> block_42 (dispatcher bypassed)
            >>> target = emulator.resolve_target(context, block_5, dispatcher)
            >>> assert target == block_42
        """
        # This is a placeholder for the actual implementation
        # The real implementation would use MopTracker and MicroCodeInterpreter
        # from the existing d810.hexrays.tracker and d810.expr.emulator modules
        context.logger.debug(
            "Resolving target for block %s through dispatcher at %s",
            from_block.serial,
            dispatcher.entry_block.serial
        )
        # TODO: Implement using existing MopTracker and MicroCodeInterpreter
        return None


class CFGPatcher:
    """Applies changes to the control-flow graph.

    This service encapsulates all CFG modification logic, making it easy to:
    - Test in isolation (mocking is straightforward)
    - Audit for correctness (all graph changes in one place)
    - Extend with new types of patches

    All methods are static because they don't need instance state - they
    operate purely on the provided mba and blocks.
    """

    @staticmethod
    def redirect_edge(
        context: OptimizationContext,
        from_block: ida_hexrays.mblock_t,
        to_block: ida_hexrays.mblock_t
    ) -> int:
        """Redirect a block's outgoing edge to a new target.

        This is the fundamental operation for control-flow unflattening:
        changing a block that jumps to the dispatcher to instead jump
        directly to its actual target.

        Args:
            context: The optimization context.
            from_block: The block whose outgoing edge will be changed.
            to_block: The new target block.

        Returns:
            The number of changes made (typically 1 if successful, 0 if no-op).

        Example:
            >>> # Unflatten: block_5 -> dispatcher -> block_42
            >>> # Becomes:   block_5 -> block_42
            >>> changes = CFGPatcher.redirect_edge(context, block_5, block_42)
        """
        # This would use the existing cfg_utils functions
        # from d810.hexrays.cfg_utils import change_1way_block_successor
        context.logger.debug(
            "Redirecting block %s to %s",
            from_block.serial,
            to_block.serial
        )
        # TODO: Implement using existing cfg_utils
        return 0

    @staticmethod
    def insert_intermediate_block(
        context: OptimizationContext,
        before_block: ida_hexrays.mblock_t,
        after_block: ida_hexrays.mblock_t,
        instructions: List[ida_hexrays.minsn_t]
    ) -> ida_hexrays.mblock_t:
        """Insert a new block between two existing blocks.

        Sometimes the dispatcher performs computations that need to be
        preserved when unflattening. This method creates a new block
        containing those instructions and inserts it in the CFG.

        Args:
            context: The optimization context.
            before_block: The block that will jump to the new block.
            after_block: The block that the new block will jump to.
            instructions: The instructions to place in the new block.

        Returns:
            The newly created block.

        Example:
            >>> # The dispatcher does: x = x + 1; jump to block_42
            >>> # We need to preserve that computation
            >>> new_blk = CFGPatcher.insert_intermediate_block(
            ...     context, block_5, block_42, [add_instruction])
        """
        # This would use the existing create_block function
        # from d810.hexrays.cfg_utils import create_block
        context.logger.debug(
            "Inserting intermediate block between %s and %s with %d instructions",
            before_block.serial,
            after_block.serial,
            len(instructions)
        )
        # TODO: Implement using existing cfg_utils.create_block
        return before_block  # Placeholder

    @staticmethod
    def ensure_unconditional_predecessor(
        context: OptimizationContext,
        child: ida_hexrays.mblock_t
    ) -> int:
        """Ensure all predecessors of a block are unconditional jumps.

        Some optimizations require that predecessor blocks end with
        unconditional jumps (goto) rather than conditional jumps.
        This method transforms the CFG to meet that requirement.

        Args:
            context: The optimization context.
            child: The block whose predecessors should be made unconditional.

        Returns:
            The number of changes made.

        Example:
            >>> # Before: block_5 ends with conditional jump to dispatcher
            >>> # After:  block_5 -> new_block (unconditional) -> dispatcher
            >>> changes = CFGPatcher.ensure_unconditional_predecessor(context, dispatcher_block)
        """
        # This would use ensure_child_has_an_unconditional_father
        # from d810.hexrays.cfg_utils
        context.logger.debug(
            "Ensuring unconditional predecessors for block %s",
            child.serial
        )
        # TODO: Implement using existing cfg_utils
        return 0
