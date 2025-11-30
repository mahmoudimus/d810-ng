"""Tests for the centralized OptimizerManager.

These tests demonstrate how the manager simplifies coordination and
makes the optimization pipeline more testable and maintainable.
"""

from unittest.mock import Mock, call
import pytest

from d810.optimizers.core import OptimizationContext, OptimizationRule
from d810.optimizers.manager import (
    OptimizerManager,
    RuleRegistry,
    OptimizationStatistics,
    create_default_manager,
)


class MockRule:
    """Mock rule for testing that implements the OptimizationRule protocol."""

    def __init__(self, name, changes_per_call=1):
        self.name = name
        self.changes_per_call = changes_per_call
        self.call_count = 0

    def apply(self, context, element):
        self.call_count += 1
        return self.changes_per_call


class TestRuleRegistry:
    """Tests for the RuleRegistry data structure."""

    def test_empty_registry(self):
        registry = RuleRegistry()
        assert registry.count() == 0
        assert len(registry.all_rules()) == 0

    def test_register_different_rule_types(self):
        registry = RuleRegistry()

        flow_rule = MockRule("flow1")
        instruction_rule = MockRule("inst1")
        pattern_rule = MockRule("pattern1")

        registry.flow_rules.append(flow_rule)
        registry.instruction_rules.append(instruction_rule)
        registry.pattern_rules.append(pattern_rule)

        assert registry.count() == 3
        assert flow_rule in registry.all_rules()
        assert instruction_rule in registry.all_rules()
        assert pattern_rule in registry.all_rules()


class TestOptimizationStatistics:
    """Tests for optimization statistics tracking."""

    def test_empty_statistics(self):
        stats = OptimizationStatistics()
        assert stats.total_passes == 0
        assert len(stats.rules_applied) == 0
        assert len(stats.changes_made) == 0

    def test_record_application(self):
        stats = OptimizationStatistics()

        stats.record_application("rule1", 5)
        stats.record_application("rule1", 3)
        stats.record_application("rule2", 0)

        assert stats.rules_applied["rule1"] == 2
        assert stats.changes_made["rule1"] == 8
        assert stats.rules_applied["rule2"] == 1
        assert stats.changes_made["rule2"] == 0

    def test_summary_generation(self):
        stats = OptimizationStatistics()
        stats.total_passes = 5
        stats.record_application("XorRule", 100)
        stats.record_application("NegRule", 50)

        summary = stats.get_summary()

        assert "Total passes: 5" in summary
        assert "XorRule" in summary
        assert "100 changes" in summary


class TestOptimizerManager:
    """Tests for the centralized OptimizerManager."""

    def test_initialization(self):
        config = {"test": "value"}
        manager = OptimizerManager(config, log_dir="/tmp/test")

        assert manager.config == config
        assert manager.log_dir == "/tmp/test"
        assert manager.registry.count() == 0

    def test_register_rules(self):
        manager = OptimizerManager({})

        flow_rule = MockRule("flow1")
        inst_rule = MockRule("inst1")
        pattern_rule = MockRule("pattern1")

        manager.register_flow_rule(flow_rule)
        manager.register_instruction_rule(inst_rule)
        manager.register_pattern_rule(pattern_rule)

        assert len(manager.registry.flow_rules) == 1
        assert len(manager.registry.instruction_rules) == 1
        assert len(manager.registry.pattern_rules) == 1

    def test_optimize_with_flow_rule(self):
        """Test that flow rules are applied to the entry block."""
        manager = OptimizerManager({})
        flow_rule = MockRule("TestFlowRule", changes_per_call=5)
        manager.register_flow_rule(flow_rule)

        # Create mock mba with one block
        mock_mba = Mock()
        mock_block = Mock(serial=0)
        mock_mba.get_mblock.return_value = mock_block
        mock_mba.qty = 1

        changes = manager.optimize(mock_mba, maturity=0)

        assert changes == 5
        assert flow_rule.call_count == 1
        assert manager.statistics.rules_applied["TestFlowRule"] == 1
        assert manager.statistics.changes_made["TestFlowRule"] == 5

    def test_optimize_with_instruction_rule(self):
        """Test that instruction rules are applied to all instructions."""
        manager = OptimizerManager({})
        inst_rule = MockRule("TestInstRule", changes_per_call=1)
        manager.register_instruction_rule(inst_rule)

        # Create mock mba with one block containing 3 instructions
        mock_mba = Mock()
        mock_mba.qty = 1

        # Create chain of 3 instructions
        ins1 = Mock()
        ins2 = Mock()
        ins3 = Mock()
        ins1.next = ins2
        ins2.next = ins3
        ins3.next = None

        mock_block = Mock(serial=0, head=ins1)
        mock_mba.get_mblock.return_value = mock_block

        changes = manager.optimize(mock_mba, maturity=0)

        # Should be called 3 times (once per instruction)
        assert changes == 3
        assert inst_rule.call_count == 3

    def test_optimize_with_multiple_blocks(self):
        """Test that rules are applied to all blocks."""
        manager = OptimizerManager({})
        inst_rule = MockRule("TestInstRule", changes_per_call=1)
        manager.register_instruction_rule(inst_rule)

        # Create mock mba with 3 blocks, each with 2 instructions
        mock_mba = Mock()
        mock_mba.qty = 3

        blocks = []
        for i in range(3):
            ins1 = Mock()
            ins2 = Mock()
            ins1.next = ins2
            ins2.next = None
            block = Mock(serial=i, head=ins1)
            blocks.append(block)

        mock_mba.get_mblock.side_effect = blocks

        changes = manager.optimize(mock_mba, maturity=0)

        # 3 blocks × 2 instructions = 6 calls
        assert changes == 6
        assert inst_rule.call_count == 6

    def test_error_handling_continues_optimization(self):
        """Test that errors in one rule don't stop other rules."""
        manager = OptimizerManager({})

        # Rule that throws an error
        bad_rule = Mock(spec=OptimizationRule)
        bad_rule.name = "BadRule"
        bad_rule.apply.side_effect = RuntimeError("Test error")

        # Rule that works fine
        good_rule = MockRule("GoodRule", changes_per_call=1)

        manager.register_instruction_rule(bad_rule)
        manager.register_instruction_rule(good_rule)

        # Create simple mock mba
        mock_mba = Mock()
        mock_mba.qty = 1
        ins = Mock()
        ins.next = None
        block = Mock(serial=0, head=ins)
        mock_mba.get_mblock.return_value = block

        # Should complete despite error in bad_rule
        changes = manager.optimize(mock_mba, maturity=0)

        assert changes == 1  # Only good_rule made changes
        assert good_rule.call_count == 1

    def test_cache_loader_hook(self):
        """Test that cache loader is called and can skip optimization."""
        manager = OptimizerManager({})
        rule = MockRule("TestRule", changes_per_call=5)
        manager.register_flow_rule(rule)

        # Set up cache loader that returns cached result
        cache_loader = Mock(return_value=42)
        manager.set_cache_handlers(loader=cache_loader)

        mock_mba = Mock()
        changes = manager.optimize(mock_mba, maturity=0)

        # Should return cached result without calling rule
        assert changes == 42
        cache_loader.assert_called_once_with(mock_mba, 0)
        assert rule.call_count == 0

    def test_cache_saver_hook(self):
        """Test that cache saver is called after optimization."""
        manager = OptimizerManager({})
        rule = MockRule("TestRule", changes_per_call=5)
        manager.register_flow_rule(rule)

        cache_saver = Mock()
        manager.set_cache_handlers(saver=cache_saver)

        mock_mba = Mock()
        mock_mba.get_mblock.return_value = Mock(serial=0)
        mock_mba.qty = 1

        changes = manager.optimize(mock_mba, maturity=0)

        # Should save result to cache
        assert changes == 5
        cache_saver.assert_called_once_with(mock_mba, 0, 5)

    def test_profiling_hooks(self):
        """Test that profiling hooks are called."""
        manager = OptimizerManager({})
        rule = MockRule("TestRule", changes_per_call=3)
        manager.register_flow_rule(rule)

        pre_hook = Mock()
        post_hook = Mock()
        manager.set_profiling_hooks(pre_hook=pre_hook, post_hook=post_hook)

        mock_mba = Mock()
        mock_mba.get_mblock.return_value = Mock(serial=0)
        mock_mba.qty = 1

        changes = manager.optimize(mock_mba, maturity=0)

        # Hooks should be called
        assert pre_hook.call_count == 1
        assert post_hook.call_count == 1

        # Check that context was passed to pre_hook
        context = pre_hook.call_args[0][0]
        assert isinstance(context, OptimizationContext)

        # Check that changes were passed to post_hook
        _, post_changes = post_hook.call_args[0]
        assert post_changes == 3

    def test_statistics_tracking(self):
        """Test that statistics are properly tracked across multiple passes."""
        manager = OptimizerManager({})
        rule1 = MockRule("Rule1", changes_per_call=5)
        rule2 = MockRule("Rule2", changes_per_call=3)
        manager.register_flow_rule(rule1)
        manager.register_flow_rule(rule2)

        mock_mba = Mock()
        mock_mba.get_mblock.return_value = Mock(serial=0)
        mock_mba.qty = 1

        # Run multiple passes
        manager.optimize(mock_mba, maturity=0)
        manager.optimize(mock_mba, maturity=1)

        stats = manager.get_statistics()

        assert stats.total_passes == 2
        assert stats.rules_applied["Rule1"] == 2
        assert stats.rules_applied["Rule2"] == 2
        assert stats.changes_made["Rule1"] == 10  # 5 × 2
        assert stats.changes_made["Rule2"] == 6   # 3 × 2

    def test_reset_statistics(self):
        """Test that statistics can be reset."""
        manager = OptimizerManager({})
        rule = MockRule("TestRule", changes_per_call=1)
        manager.register_flow_rule(rule)

        mock_mba = Mock()
        mock_mba.get_mblock.return_value = Mock(serial=0)
        mock_mba.qty = 1

        manager.optimize(mock_mba, maturity=0)
        assert manager.statistics.total_passes == 1

        manager.reset_statistics()
        assert manager.statistics.total_passes == 0


class TestFactoryFunction:
    """Tests for the factory function."""

    def test_create_default_manager(self):
        manager = create_default_manager()

        assert isinstance(manager, OptimizerManager)
        assert manager.config == {}

    def test_create_manager_with_config(self):
        config = {"test": "value"}
        manager = create_default_manager(config)

        assert manager.config == config


"""
Benefits Demonstrated by These Tests
=====================================

1. **No IDA dependency**: All tests use mocks, run instantly
2. **Clear behavior**: Each test verifies one specific behavior
3. **Easy to extend**: Adding new test cases is straightforward
4. **Comprehensive coverage**: Can test edge cases easily

Compare to testing the old scattered approach:
- Would need full IDA environment
- Hard to isolate individual behaviors
- Slow test execution
- Difficult to test error handling

The OptimizerManager makes the entire optimization pipeline testable
without needing actual microcode or IDA infrastructure.
"""
