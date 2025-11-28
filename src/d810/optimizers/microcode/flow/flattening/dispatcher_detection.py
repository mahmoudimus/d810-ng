"""
Dispatcher Block Detection Cache

This module provides a unified, cached dispatcher detection system that aggregates
multiple detection strategies for identifying state machine dispatcher blocks in
control flow flattened code.

Detection Strategies:
1. High Fan-In: Blocks with ≥N predecessors (typical for dispatchers)
2. State Comparison: Blocks comparing a variable against large constants (>0x10000)
3. Loop Header: Blocks that are natural loop headers (dominator-based)
4. Predecessor Uniformity: Most predecessors are unconditional jumps
5. Constant Frequency: Blocks compared against many unique constants
6. Back-edge Detection: Blocks with incoming back-edges from dominated blocks

Usage:
    cache = DispatcherCache.get_or_create(mba)
    info = cache.analyze()

    # Check if a block is a dispatcher
    if cache.is_dispatcher(blk.serial):
        ...

    # Force refresh
    cache.refresh()
"""
from __future__ import annotations

import weakref
from dataclasses import dataclass, field
from enum import IntFlag
from typing import TYPE_CHECKING

import ida_hexrays

from d810.core import getLogger

if TYPE_CHECKING:
    pass

logger = getLogger("D810.dispatcher")


class DispatcherStrategy(IntFlag):
    """Flags indicating which strategies detected a block as a dispatcher."""
    NONE = 0
    HIGH_FAN_IN = 1 << 0           # ≥N predecessors
    STATE_COMPARISON = 1 << 1      # Compares against large constants
    LOOP_HEADER = 1 << 2           # Natural loop header
    PREDECESSOR_UNIFORM = 1 << 3  # Most preds are unconditional jumps
    CONSTANT_FREQUENCY = 1 << 4   # Many unique constants compared
    BACK_EDGE = 1 << 5            # Has incoming back-edges
    NESTED_LOOP = 1 << 6          # Part of nested loop structure (Hodur)


@dataclass
class BlockAnalysis:
    """Analysis results for a single block."""
    serial: int
    strategies: DispatcherStrategy = DispatcherStrategy.NONE
    score: float = 0.0

    # Strategy-specific data
    predecessor_count: int = 0
    unconditional_pred_count: int = 0
    state_constants: set[int] = field(default_factory=set)
    back_edge_sources: list[int] = field(default_factory=list)
    loop_depth: int = 0

    @property
    def is_dispatcher(self) -> bool:
        """True if any strategy flagged this block as a dispatcher."""
        return self.strategies != DispatcherStrategy.NONE

    @property
    def is_strong_dispatcher(self) -> bool:
        """True if multiple strategies agree this is a dispatcher."""
        # Count set bits
        count = bin(self.strategies).count('1')
        return count >= 2


@dataclass
class StateVariableCandidate:
    """A candidate for the state variable."""
    mop: ida_hexrays.mop_t
    init_value: int | None = None
    comparison_count: int = 0
    assignment_count: int = 0
    unique_constants: set[int] = field(default_factory=set)
    comparison_blocks: list[int] = field(default_factory=list)
    assignment_blocks: list[int] = field(default_factory=list)
    score: float = 0.0


@dataclass
class DispatcherAnalysis:
    """Complete dispatcher analysis for a function."""
    func_ea: int
    maturity: int

    # Analysis results
    blocks: dict[int, BlockAnalysis] = field(default_factory=dict)
    dispatchers: list[int] = field(default_factory=list)  # Block serials flagged as dispatchers
    state_variable: StateVariableCandidate | None = None
    state_constants: set[int] = field(default_factory=set)

    # Hodur-specific
    is_hodur_style: bool = False
    initial_state: int | None = None
    nested_loop_depth: int = 0


# Thresholds for detection strategies
MIN_HIGH_FAN_IN = 5
MIN_STATE_CONSTANT = 0x10000
MIN_UNIQUE_CONSTANTS = 3
MIN_PREDECESSOR_UNIFORMITY_RATIO = 0.8
MIN_BACK_EDGE_RATIO = 0.3


class DispatcherCache:
    """
    Per-function cache for dispatcher detection results.

    The cache is keyed by (func_ea, maturity) to handle IDA's multiple decompilation passes.
    """

    # Class-level cache: func_ea -> weakref(DispatcherCache)
    _cache: dict[int, "DispatcherCache"] = {}

    def __init__(self, mba: ida_hexrays.mba_t):
        self.mba = mba
        self.func_ea = mba.entry_ea
        self._analysis: DispatcherAnalysis | None = None
        self._last_maturity: int = -1

    @classmethod
    def get_or_create(cls, mba: ida_hexrays.mba_t) -> "DispatcherCache":
        """Get cached instance or create new one for this function."""
        func_ea = mba.entry_ea

        if func_ea in cls._cache:
            cache = cls._cache[func_ea]
            cache.mba = mba  # Update mba reference
            # Check if maturity changed (need re-analysis)
            if cache._last_maturity != mba.maturity:
                cache._analysis = None  # Invalidate
            return cache

        cache = cls(mba)
        cls._cache[func_ea] = cache
        return cache

    @classmethod
    def clear_cache(cls, func_ea: int | None = None) -> None:
        """Clear cache for a specific function or all functions."""
        if func_ea is None:
            cls._cache.clear()
        elif func_ea in cls._cache:
            del cls._cache[func_ea]

    def refresh(self) -> DispatcherAnalysis:
        """Force re-analysis."""
        self._analysis = None
        return self.analyze()

    def analyze(self) -> DispatcherAnalysis:
        """Analyze the function and return dispatcher information."""
        if self._analysis is not None and self._last_maturity == self.mba.maturity:
            return self._analysis

        logger.debug("Analyzing function 0x%x at maturity %d", self.func_ea, self.mba.maturity)

        analysis = DispatcherAnalysis(
            func_ea=self.func_ea,
            maturity=self.mba.maturity,
        )

        # Quick check: does this function have a switch/jtbl? If so, it's O-LLVM style
        # and we can skip expensive analysis (O-LLVM doesn't need dispatcher skipping)
        has_jtbl = False
        for i in range(self.mba.qty):
            blk = self.mba.get_mblock(i)
            if blk.tail and blk.tail.opcode == ida_hexrays.m_jtbl:
                has_jtbl = True
                break

        if has_jtbl:
            # O-LLVM style - no need for full analysis
            analysis.is_hodur_style = False
            self._analysis = analysis
            self._last_maturity = self.mba.maturity
            logger.debug("Detected jtbl - O-LLVM style, skipping Hodur analysis")
            return analysis

        # Run all detection strategies for potential Hodur-style
        self._analyze_block_predecessors(analysis)
        self._analyze_state_comparisons(analysis)
        self._analyze_loop_structure(analysis)
        self._analyze_state_assignments(analysis)
        self._score_blocks(analysis)
        self._detect_hodur_pattern(analysis)

        # Collect dispatcher blocks
        for serial, block_info in analysis.blocks.items():
            if block_info.is_dispatcher:
                analysis.dispatchers.append(serial)

        self._analysis = analysis
        self._last_maturity = self.mba.maturity

        logger.info(
            "Dispatcher analysis complete: %d dispatchers, %d state constants, hodur=%s",
            len(analysis.dispatchers),
            len(analysis.state_constants),
            analysis.is_hodur_style,
        )

        return analysis

    def is_dispatcher(self, serial: int) -> bool:
        """Check if a block is flagged as a dispatcher."""
        analysis = self.analyze()
        if serial in analysis.blocks:
            return analysis.blocks[serial].is_dispatcher
        return False

    def get_block_info(self, serial: int) -> BlockAnalysis | None:
        """Get analysis info for a specific block."""
        analysis = self.analyze()
        return analysis.blocks.get(serial)

    def _get_or_create_block(self, analysis: DispatcherAnalysis, serial: int) -> BlockAnalysis:
        """Get or create BlockAnalysis for a serial."""
        if serial not in analysis.blocks:
            analysis.blocks[serial] = BlockAnalysis(serial=serial)
        return analysis.blocks[serial]

    def _analyze_block_predecessors(self, analysis: DispatcherAnalysis) -> None:
        """Strategy 1: High fan-in detection."""
        for i in range(self.mba.qty):
            blk = self.mba.get_mblock(i)
            pred_count = blk.npred()

            if pred_count >= MIN_HIGH_FAN_IN:
                block_info = self._get_or_create_block(analysis, i)
                block_info.predecessor_count = pred_count
                block_info.strategies |= DispatcherStrategy.HIGH_FAN_IN

                # Count unconditional predecessors (goto blocks)
                uncond_count = 0
                for pred_serial in blk.predset:
                    pred_blk = self.mba.get_mblock(pred_serial)
                    if pred_blk.tail and pred_blk.tail.opcode == ida_hexrays.m_goto:
                        uncond_count += 1
                    elif pred_blk.nsucc() == 1:
                        uncond_count += 1

                block_info.unconditional_pred_count = uncond_count

                # Check predecessor uniformity
                if pred_count > 0 and uncond_count / pred_count >= MIN_PREDECESSOR_UNIFORMITY_RATIO:
                    block_info.strategies |= DispatcherStrategy.PREDECESSOR_UNIFORM

    def _analyze_state_comparisons(self, analysis: DispatcherAnalysis) -> None:
        """Strategy 2: State comparison detection."""
        # Track which variables are compared against large constants
        comparison_opcodes = [
            ida_hexrays.m_jnz, ida_hexrays.m_jz,
            ida_hexrays.m_jae, ida_hexrays.m_jb,
            ida_hexrays.m_ja, ida_hexrays.m_jbe,
            ida_hexrays.m_jge, ida_hexrays.m_jg,
            ida_hexrays.m_jl, ida_hexrays.m_jle,
        ]

        # var_key -> list of (block_serial, constant_value)
        var_comparisons: dict[str, list[tuple[int, int]]] = {}

        for i in range(self.mba.qty):
            blk = self.mba.get_mblock(i)
            if blk.tail and blk.tail.opcode in comparison_opcodes:
                # Check right operand is a large constant
                if blk.tail.r.t == ida_hexrays.mop_n:
                    const_val = blk.tail.r.nnn.value
                    if const_val > MIN_STATE_CONSTANT:
                        # Get variable key from left operand
                        var_key = self._get_mop_key(blk.tail.l)
                        if var_key:
                            if var_key not in var_comparisons:
                                var_comparisons[var_key] = []
                            var_comparisons[var_key].append((i, const_val))

                            block_info = self._get_or_create_block(analysis, i)
                            block_info.state_constants.add(const_val)
                            analysis.state_constants.add(const_val)

        # Find the state variable (most comparisons)
        best_var_key = None
        best_comparisons = []
        for var_key, comparisons in var_comparisons.items():
            if len(comparisons) > len(best_comparisons):
                best_var_key = var_key
                best_comparisons = comparisons

        # Mark blocks with state comparisons
        if len(best_comparisons) >= MIN_UNIQUE_CONSTANTS:
            unique_constants = {c[1] for c in best_comparisons}

            for blk_serial, const_val in best_comparisons:
                block_info = self._get_or_create_block(analysis, blk_serial)
                block_info.strategies |= DispatcherStrategy.STATE_COMPARISON

                # Mark as high constant frequency if many unique constants
                if len(unique_constants) >= MIN_UNIQUE_CONSTANTS:
                    block_info.strategies |= DispatcherStrategy.CONSTANT_FREQUENCY

    def _analyze_loop_structure(self, analysis: DispatcherAnalysis) -> None:
        """Strategy 3 & 6: Loop header and back-edge detection."""
        # Simple back-edge detection: if block B jumps to block A where A.serial <= B.serial
        # and A dominates B (approximately: A is reachable from entry before B)

        for i in range(self.mba.qty):
            blk = self.mba.get_mblock(i)

            for succ_serial in blk.succset:
                # Back-edge: jumping to an earlier block
                if succ_serial <= i:
                    target_info = self._get_or_create_block(analysis, succ_serial)
                    target_info.back_edge_sources.append(i)
                    target_info.strategies |= DispatcherStrategy.BACK_EDGE

                    # If many back-edges, likely a loop header
                    if len(target_info.back_edge_sources) >= 2:
                        target_info.strategies |= DispatcherStrategy.LOOP_HEADER

        # Detect nested loop structure (Hodur pattern)
        self._detect_nested_loops(analysis)

    def _detect_nested_loops(self, analysis: DispatcherAnalysis) -> None:
        """Detect nested while(1) loop pattern characteristic of Hodur."""
        # Hodur uses deeply nested while(1) loops
        # Look for blocks that are loop headers at multiple nesting levels

        # Simple heuristic: count blocks with back-edges that are also
        # targets of other back-edge blocks
        loop_headers = [
            serial for serial, info in analysis.blocks.items()
            if DispatcherStrategy.BACK_EDGE in info.strategies
        ]

        if len(loop_headers) >= 3:
            # Check for nesting
            nested_count = 0
            for header in loop_headers:
                header_info = analysis.blocks[header]
                # Check if any back-edge source is also a loop header
                for src in header_info.back_edge_sources:
                    if src in loop_headers:
                        nested_count += 1

            if nested_count >= 2:
                analysis.nested_loop_depth = nested_count
                # Mark deepest loop headers
                for header in loop_headers:
                    analysis.blocks[header].strategies |= DispatcherStrategy.NESTED_LOOP

    def _analyze_state_assignments(self, analysis: DispatcherAnalysis) -> None:
        """Find state variable assignments for Hodur detection."""
        if not analysis.state_constants:
            return

        # Find mov instructions assigning state constants
        for i in range(self.mba.qty):
            blk = self.mba.get_mblock(i)
            insn = blk.head
            while insn:
                if insn.opcode == ida_hexrays.m_mov:
                    if insn.l.t == ida_hexrays.mop_n:
                        const_val = insn.l.nnn.value
                        if const_val in analysis.state_constants:
                            # This block assigns a state constant
                            block_info = self._get_or_create_block(analysis, i)
                            block_info.state_constants.add(const_val)
                insn = insn.next

    def _score_blocks(self, analysis: DispatcherAnalysis) -> None:
        """Calculate dispatcher likelihood score for each block."""
        for serial, block_info in analysis.blocks.items():
            score = 0.0

            # High fan-in: +10 per predecessor over threshold
            if DispatcherStrategy.HIGH_FAN_IN in block_info.strategies:
                score += (block_info.predecessor_count - MIN_HIGH_FAN_IN + 1) * 10

            # State comparison: +20
            if DispatcherStrategy.STATE_COMPARISON in block_info.strategies:
                score += 20

            # Loop header: +15
            if DispatcherStrategy.LOOP_HEADER in block_info.strategies:
                score += 15

            # Predecessor uniformity: +10
            if DispatcherStrategy.PREDECESSOR_UNIFORM in block_info.strategies:
                score += 10

            # Constant frequency: +5 per unique constant
            if DispatcherStrategy.CONSTANT_FREQUENCY in block_info.strategies:
                score += len(block_info.state_constants) * 5

            # Back-edge: +10 per back-edge
            if DispatcherStrategy.BACK_EDGE in block_info.strategies:
                score += len(block_info.back_edge_sources) * 10

            # Nested loop: +25 (Hodur signature)
            if DispatcherStrategy.NESTED_LOOP in block_info.strategies:
                score += 25

            block_info.score = score

    def _detect_hodur_pattern(self, analysis: DispatcherAnalysis) -> None:
        """Detect if this is Hodur-style flattening."""
        # Hodur characteristics:
        # 1. Nested while(1) loops (not switch)
        # 2. State comparisons using jnz/jz (not jtbl)
        # 3. Large 32-bit constants
        # 4. Many state transitions

        hodur_score = 0

        # Nested loops
        if analysis.nested_loop_depth >= 2:
            hodur_score += 30

        # State constants count
        if len(analysis.state_constants) >= MIN_UNIQUE_CONSTANTS:
            hodur_score += len(analysis.state_constants) * 5

        # No jtbl (switch) present - check for absence of jtbl opcode
        has_jtbl = False
        for i in range(self.mba.qty):
            blk = self.mba.get_mblock(i)
            if blk.tail and blk.tail.opcode == ida_hexrays.m_jtbl:
                has_jtbl = True
                break

        if not has_jtbl and len(analysis.state_constants) >= MIN_UNIQUE_CONSTANTS:
            hodur_score += 20

        analysis.is_hodur_style = hodur_score >= 50

        if analysis.is_hodur_style:
            logger.info("Detected Hodur-style flattening (score=%d)", hodur_score)

            # Find initial state
            self._find_initial_state(analysis)

    def _find_initial_state(self, analysis: DispatcherAnalysis) -> None:
        """Find the initial state value for Hodur."""
        # Look in early blocks for assignment of a state constant
        for i in range(min(5, self.mba.qty)):
            blk = self.mba.get_mblock(i)
            insn = blk.head
            while insn:
                if insn.opcode == ida_hexrays.m_mov:
                    if insn.l.t == ida_hexrays.mop_n:
                        const_val = insn.l.nnn.value
                        if const_val in analysis.state_constants:
                            analysis.initial_state = const_val
                            logger.debug("Found initial state: 0x%x in block %d", const_val, i)
                            return
                insn = insn.next

    def _get_mop_key(self, mop: ida_hexrays.mop_t) -> str | None:
        """Get a unique key for an mop_t for comparison."""
        if mop.t == ida_hexrays.mop_r:
            return f"r{mop.r}"
        elif mop.t == ida_hexrays.mop_S:
            return f"S{mop.s.off}"
        elif mop.t == ida_hexrays.mop_v:
            return f"v{mop.g}"
        elif mop.t == ida_hexrays.mop_l:
            return f"l{mop.l.off}"
        return None


def should_skip_dispatcher(mba: ida_hexrays.mba_t, blk: ida_hexrays.mblock_t) -> bool:
    """
    Convenience function to check if a block should be skipped for O-LLVM style patching.

    This is used by FixPredecessorOfConditionalJumpBlock to avoid cascading unreachability
    when dealing with Hodur-style state machines.

    IMPORTANT: This should only return True for Hodur-style functions, NOT for O-LLVM.
    O-LLVM patching requires modifying dispatcher blocks, so we must not skip them.
    """
    cache = DispatcherCache.get_or_create(mba)
    analysis = cache.analyze()

    # Only skip if this is Hodur-style flattening (nested while loops, no switch/jtbl)
    # O-LLVM style should NOT be skipped - it needs the predecessor patching
    if not analysis.is_hodur_style:
        return False

    # For Hodur-style, skip blocks flagged as dispatchers
    if cache.is_dispatcher(blk.serial):
        return True

    return False
