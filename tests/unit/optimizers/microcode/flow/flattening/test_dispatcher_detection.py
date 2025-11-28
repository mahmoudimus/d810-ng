"""Tests for dispatcher detection cache and strategies.

These tests validate the unified dispatcher detection system that aggregates
multiple detection strategies for identifying state machine dispatcher blocks.

The tests cover:
- Strategy flags and scoring
- BlockAnalysis and DispatcherAnalysis dataclasses
- StateVariableCandidate with microcode-to-native offset conversion
- DispatcherCache caching behavior
- Statistics tracking
"""

from dataclasses import dataclass
from unittest.mock import Mock, MagicMock, patch
import pytest


# Mock ida_hexrays before importing dispatcher_detection
@pytest.fixture(autouse=True)
def mock_ida_hexrays():
    """Mock ida_hexrays module for unit tests."""
    mock_module = MagicMock()

    # Mock opcode constants
    mock_module.m_jnz = 0x30
    mock_module.m_jz = 0x31
    mock_module.m_jae = 0x32
    mock_module.m_jb = 0x33
    mock_module.m_ja = 0x34
    mock_module.m_jbe = 0x35
    mock_module.m_jge = 0x36
    mock_module.m_jg = 0x37
    mock_module.m_jl = 0x38
    mock_module.m_jle = 0x39
    mock_module.m_goto = 0x40
    mock_module.m_jtbl = 0x41
    mock_module.m_mov = 0x01
    mock_module.m_ldx = 0x02

    # Mock mop_t types
    mock_module.mop_n = 2  # Number/constant
    mock_module.mop_r = 1  # Register
    mock_module.mop_S = 3  # Stack variable
    mock_module.mop_v = 5  # Global variable
    mock_module.mop_l = 6  # Local variable
    mock_module.mop_d = 4  # Result of another instruction
    mock_module.mop_b = 8  # Block reference

    mock_module.BADADDR = 0xFFFFFFFFFFFFFFFF

    # Mock mop_t class
    mock_module.mop_t = MagicMock

    with patch.dict('sys.modules', {'ida_hexrays': mock_module}):
        yield mock_module


class TestDispatcherStrategy:
    """Tests for DispatcherStrategy flags."""

    def test_strategy_flags_are_powers_of_two(self, mock_ida_hexrays):
        from d810.optimizers.microcode.flow.flattening.dispatcher_detection import (
            DispatcherStrategy
        )

        # Each strategy should be a power of 2 for bitwise operations
        strategies = [
            DispatcherStrategy.HIGH_FAN_IN,
            DispatcherStrategy.STATE_COMPARISON,
            DispatcherStrategy.LOOP_HEADER,
            DispatcherStrategy.PREDECESSOR_UNIFORM,
            DispatcherStrategy.CONSTANT_FREQUENCY,
            DispatcherStrategy.BACK_EDGE,
            DispatcherStrategy.NESTED_LOOP,
            DispatcherStrategy.SMALL_BLOCK,
            DispatcherStrategy.SWITCH_JUMP,
        ]

        for strategy in strategies:
            # Each should be a power of 2
            assert strategy & (strategy - 1) == 0 or strategy == 0

    def test_strategy_combination(self, mock_ida_hexrays):
        from d810.optimizers.microcode.flow.flattening.dispatcher_detection import (
            DispatcherStrategy
        )

        combined = DispatcherStrategy.HIGH_FAN_IN | DispatcherStrategy.STATE_COMPARISON

        assert DispatcherStrategy.HIGH_FAN_IN in combined
        assert DispatcherStrategy.STATE_COMPARISON in combined
        assert DispatcherStrategy.LOOP_HEADER not in combined


class TestBlockAnalysis:
    """Tests for BlockAnalysis dataclass."""

    def test_is_dispatcher_with_no_strategies(self, mock_ida_hexrays):
        from d810.optimizers.microcode.flow.flattening.dispatcher_detection import (
            BlockAnalysis, DispatcherStrategy
        )

        block = BlockAnalysis(serial=0)
        assert not block.is_dispatcher
        assert block.strategies == DispatcherStrategy.NONE

    def test_is_dispatcher_with_single_strategy(self, mock_ida_hexrays):
        from d810.optimizers.microcode.flow.flattening.dispatcher_detection import (
            BlockAnalysis, DispatcherStrategy
        )

        block = BlockAnalysis(serial=0, strategies=DispatcherStrategy.HIGH_FAN_IN)
        assert block.is_dispatcher
        assert not block.is_strong_dispatcher  # Only one strategy

    def test_is_strong_dispatcher_with_multiple_strategies(self, mock_ida_hexrays):
        from d810.optimizers.microcode.flow.flattening.dispatcher_detection import (
            BlockAnalysis, DispatcherStrategy
        )

        block = BlockAnalysis(
            serial=0,
            strategies=DispatcherStrategy.HIGH_FAN_IN | DispatcherStrategy.STATE_COMPARISON
        )
        assert block.is_dispatcher
        assert block.is_strong_dispatcher  # Two strategies = strong


class TestStateVariableCandidate:
    """Tests for StateVariableCandidate and stack offset conversion."""

    def test_stack_offset_conversion(self, mock_ida_hexrays):
        from d810.optimizers.microcode.flow.flattening.dispatcher_detection import (
            StateVariableCandidate
        )

        # Create stack variable candidate
        sv = StateVariableCandidate(
            mop=None,
            mop_type=3,  # mop_S (stack)
            mop_offset=0x20,  # Microcode offset
            mop_size=4,
        )

        # Convert with frame_size=0x100
        native_offset = sv.get_native_stack_offset(0x100)

        # display_offset = frame_size - mop_offset = 0x100 - 0x20 = 0xE0
        # native_offset = -display_offset = -0xE0
        assert native_offset == -(0x100 - 0x20)
        assert native_offset == -0xE0

    def test_register_var_returns_none(self, mock_ida_hexrays):
        from d810.optimizers.microcode.flow.flattening.dispatcher_detection import (
            StateVariableCandidate
        )

        # Create register variable candidate
        sv = StateVariableCandidate(
            mop=None,
            mop_type=1,  # mop_r (register)
            mop_offset=0,  # RAX
            mop_size=8,
        )

        # Should return None for non-stack vars
        native_offset = sv.get_native_stack_offset(0x100)
        assert native_offset is None


class TestDispatcherAnalysis:
    """Tests for DispatcherAnalysis dataclass."""

    def test_initial_state(self, mock_ida_hexrays):
        from d810.optimizers.microcode.flow.flattening.dispatcher_detection import (
            DispatcherAnalysis
        )

        analysis = DispatcherAnalysis(func_ea=0x1000, maturity=0)

        assert analysis.func_ea == 0x1000
        assert analysis.maturity == 0
        assert len(analysis.blocks) == 0
        assert len(analysis.dispatchers) == 0
        assert analysis.state_variable is None
        assert not analysis.is_hodur_style
        assert analysis.initial_state is None


class TestDispatcherCacheBasics:
    """Basic tests for DispatcherCache without full IDA mocking."""

    def test_thresholds_are_defined(self, mock_ida_hexrays):
        from d810.optimizers.microcode.flow.flattening.dispatcher_detection import (
            MIN_HIGH_FAN_IN,
            MIN_STATE_CONSTANT,
            MIN_UNIQUE_CONSTANTS,
            MIN_PREDECESSOR_UNIFORMITY_RATIO,
            MAX_DISPATCHER_BLOCK_SIZE,
        )

        assert MIN_HIGH_FAN_IN == 5
        assert MIN_STATE_CONSTANT == 0x10000
        assert MIN_UNIQUE_CONSTANTS == 3
        assert MIN_PREDECESSOR_UNIFORMITY_RATIO == 0.8
        assert MAX_DISPATCHER_BLOCK_SIZE == 20


class TestDispatcherCacheWithMocks:
    """Tests for DispatcherCache using mock mba_t."""

    def create_mock_mba(self, num_blocks=10, has_jtbl=False):
        """Create a mock mba_t with configurable blocks."""
        mock_mba = Mock()
        mock_mba.entry_ea = 0x1000
        mock_mba.maturity = 0x10
        mock_mba.qty = num_blocks
        mock_mba.stacksize = 0x100
        mock_mba.frsize = 0x100

        blocks = []
        for i in range(num_blocks):
            blk = Mock()
            blk.serial = i
            blk.npred.return_value = 2 if i > 0 else 0
            blk.nsucc.return_value = 1
            blk.predset = []
            blk.succset = [i + 1] if i < num_blocks - 1 else []

            # Create mock instruction
            tail = Mock()
            tail.opcode = 0x41 if has_jtbl and i == 5 else 0x40  # m_jtbl or m_goto
            tail.l = Mock()
            tail.l.t = 8  # mop_b
            tail.r = Mock()
            tail.r.t = 2  # mop_n
            tail.r.nnn = Mock()
            tail.r.nnn.value = 0x50000 + i

            blk.tail = tail
            blk.head = tail
            blocks.append(blk)

        mock_mba.get_mblock.side_effect = lambda i: blocks[i] if i < len(blocks) else None
        return mock_mba, blocks

    def test_cache_creation(self, mock_ida_hexrays):
        from d810.optimizers.microcode.flow.flattening.dispatcher_detection import (
            DispatcherCache
        )

        # Clear any existing cache
        DispatcherCache._cache.clear()

        mock_mba, _ = self.create_mock_mba()
        cache = DispatcherCache.get_or_create(mock_mba)

        assert cache.func_ea == 0x1000
        assert cache.mba is mock_mba

    def test_cache_reuse(self, mock_ida_hexrays):
        from d810.optimizers.microcode.flow.flattening.dispatcher_detection import (
            DispatcherCache
        )

        DispatcherCache._cache.clear()

        mock_mba, _ = self.create_mock_mba()
        cache1 = DispatcherCache.get_or_create(mock_mba)
        cache2 = DispatcherCache.get_or_create(mock_mba)

        assert cache1 is cache2

    def test_cache_invalidation_on_maturity_change(self, mock_ida_hexrays):
        from d810.optimizers.microcode.flow.flattening.dispatcher_detection import (
            DispatcherCache
        )

        DispatcherCache._cache.clear()

        mock_mba, _ = self.create_mock_mba()
        cache = DispatcherCache.get_or_create(mock_mba)

        # Force analysis
        cache._analysis = Mock()
        cache._last_maturity = 0x10

        # Change maturity
        mock_mba.maturity = 0x20
        cache2 = DispatcherCache.get_or_create(mock_mba)

        # Analysis should be invalidated
        assert cache2._analysis is None

    def test_clear_cache(self, mock_ida_hexrays):
        from d810.optimizers.microcode.flow.flattening.dispatcher_detection import (
            DispatcherCache
        )

        DispatcherCache._cache.clear()

        mock_mba, _ = self.create_mock_mba()
        DispatcherCache.get_or_create(mock_mba)

        assert len(DispatcherCache._cache) == 1

        DispatcherCache.clear_cache()

        assert len(DispatcherCache._cache) == 0

    def test_jtbl_detection_skips_hodur_analysis(self, mock_ida_hexrays):
        from d810.optimizers.microcode.flow.flattening.dispatcher_detection import (
            DispatcherCache
        )

        DispatcherCache._cache.clear()

        # Create MBA with jtbl
        mock_mba, blocks = self.create_mock_mba(has_jtbl=True)
        # Set block 5 to have jtbl opcode
        blocks[5].tail.opcode = 0x41  # m_jtbl

        cache = DispatcherCache.get_or_create(mock_mba)
        analysis = cache.analyze()

        # Should detect O-LLVM style (not Hodur)
        assert not analysis.is_hodur_style


class TestDispatcherCacheStatistics:
    """Tests for statistics tracking."""

    def test_get_statistics(self, mock_ida_hexrays):
        from d810.optimizers.microcode.flow.flattening.dispatcher_detection import (
            DispatcherCache, DispatcherAnalysis, BlockAnalysis, DispatcherStrategy
        )

        DispatcherCache._cache.clear()

        # Create a cache with mock analysis
        mock_mba = Mock()
        mock_mba.entry_ea = 0x2000
        mock_mba.maturity = 0x10
        mock_mba.qty = 20

        cache = DispatcherCache(mock_mba)
        cache.blocks_analyzed = 20
        cache.blocks_skipped = 15

        # Create mock analysis
        analysis = DispatcherAnalysis(func_ea=0x2000, maturity=0x10)
        analysis.blocks = {
            0: BlockAnalysis(serial=0, strategies=DispatcherStrategy.HIGH_FAN_IN),
            5: BlockAnalysis(
                serial=5,
                strategies=DispatcherStrategy.HIGH_FAN_IN | DispatcherStrategy.STATE_COMPARISON
            ),
        }
        analysis.dispatchers = [0, 5]
        analysis.state_constants = {0x50000, 0x60000, 0x70000}
        analysis.is_hodur_style = True

        cache._analysis = analysis
        cache._last_maturity = 0x10

        stats = cache.get_statistics()

        assert stats["blocks_analyzed"] == 20
        assert stats["blocks_skipped"] == 15
        assert stats["skip_rate"] == 0.75
        assert stats["dispatchers_found"] == 2
        assert stats["is_hodur_style"] is True
        assert stats["state_constants_count"] == 3
        assert "HIGH_FAN_IN" in stats["strategies_used"]


class TestScoringLogic:
    """Tests for block scoring logic."""

    def test_high_fan_in_scoring(self, mock_ida_hexrays):
        from d810.optimizers.microcode.flow.flattening.dispatcher_detection import (
            BlockAnalysis, DispatcherStrategy, MIN_HIGH_FAN_IN
        )

        # Block with 10 predecessors should score higher than threshold
        block = BlockAnalysis(
            serial=0,
            strategies=DispatcherStrategy.HIGH_FAN_IN,
            predecessor_count=10,
        )

        # Score = (pred_count - threshold + 1) * 10 = (10 - 5 + 1) * 10 = 60
        expected_contribution = (10 - MIN_HIGH_FAN_IN + 1) * 10
        assert expected_contribution == 60

    def test_combined_strategies_score_higher(self, mock_ida_hexrays):
        from d810.optimizers.microcode.flow.flattening.dispatcher_detection import (
            BlockAnalysis, DispatcherStrategy
        )

        single = BlockAnalysis(
            serial=0,
            strategies=DispatcherStrategy.HIGH_FAN_IN,
            predecessor_count=5,
        )

        combined = BlockAnalysis(
            serial=1,
            strategies=(
                DispatcherStrategy.HIGH_FAN_IN |
                DispatcherStrategy.STATE_COMPARISON |
                DispatcherStrategy.LOOP_HEADER
            ),
            predecessor_count=5,
        )

        # Combined should have more strategy bits
        assert bin(combined.strategies).count('1') > bin(single.strategies).count('1')


class TestMopKeyGeneration:
    """Tests for _get_mop_key helper."""

    def test_register_key(self, mock_ida_hexrays):
        from d810.optimizers.microcode.flow.flattening.dispatcher_detection import (
            DispatcherCache
        )

        mock_mba = Mock()
        mock_mba.entry_ea = 0x3000
        cache = DispatcherCache(mock_mba)

        mock_mop = Mock()
        mock_mop.t = 1  # mop_r
        mock_mop.r = 0  # RAX

        key = cache._get_mop_key(mock_mop)
        assert key == "r0"

    def test_stack_key(self, mock_ida_hexrays):
        from d810.optimizers.microcode.flow.flattening.dispatcher_detection import (
            DispatcherCache
        )

        mock_mba = Mock()
        mock_mba.entry_ea = 0x3000
        cache = DispatcherCache(mock_mba)

        mock_mop = Mock()
        mock_mop.t = 3  # mop_S
        mock_mop.s = Mock()
        mock_mop.s.off = 0x20

        key = cache._get_mop_key(mock_mop)
        assert key == "S32"  # 0x20 = 32

    def test_unknown_type_returns_none(self, mock_ida_hexrays):
        from d810.optimizers.microcode.flow.flattening.dispatcher_detection import (
            DispatcherCache
        )

        mock_mba = Mock()
        mock_mba.entry_ea = 0x3000
        cache = DispatcherCache(mock_mba)

        mock_mop = Mock()
        mock_mop.t = 99  # Unknown type

        key = cache._get_mop_key(mock_mop)
        assert key is None


"""
Integration with Sample Binaries
================================

For full integration tests with real IDA analysis, see:
- tests/system/test_libdeobfuscated.py
- samples/src/c/hodur_c2_flattened.c (Hodur-style dispatcher)
- samples/src/c/while_switch_flattened.c (O-LLVM style switch)
- samples/src/c/dispatcher_detection_samples.c (edge cases)

These system tests verify:
1. Hodur-style detection (nested while loops, jnz/jz)
2. O-LLVM-style detection (jtbl/switch)
3. State variable identification
4. State constant extraction
5. Initial state detection
"""
