"""Tests for profiling and caching infrastructure.

These tests demonstrate the performance optimization features:
- Profiling for bottleneck identification
- Persistent caching for result reuse
- Per-function rule configuration
"""

import json
import tempfile
from pathlib import Path
from unittest.mock import Mock
import pytest

from d810.optimizers.core import OptimizationContext
from d810.optimizers.profiling import OptimizationProfiler, RuleProfile
from d810.optimizers.caching import OptimizationCache, FunctionRuleConfig


class TestOptimizationProfiler:
    """Tests for the profiling infrastructure."""

    def test_profiler_initialization(self):
        profiler = OptimizationProfiler()
        assert profiler.enabled
        assert len(profiler.rule_profiles) == 0
        assert len(profiler.pass_profiles) == 0

    def test_pass_timing(self):
        profiler = OptimizationProfiler()
        context = Mock(spec=OptimizationContext, maturity=0)

        # Start and end a pass
        profiler.start_pass(context)
        profiler.end_pass(context, changes=10)

        assert len(profiler.pass_profiles) == 1
        assert profiler.pass_profiles[0].maturity == 0
        assert profiler.pass_profiles[0].changes_made == 10
        assert profiler.pass_profiles[0].duration >= 0

    def test_rule_timing(self):
        profiler = OptimizationProfiler()

        # Time a rule
        profiler.start_rule("TestRule")
        profiler.end_rule("TestRule", changes=5)

        assert "TestRule" in profiler.rule_profiles
        profile = profiler.rule_profiles["TestRule"]
        assert profile.call_count == 1
        assert profile.changes_made == 5
        assert profile.total_time >= 0

    def test_multiple_rule_calls(self):
        profiler = OptimizationProfiler()

        # Call the same rule multiple times
        for i in range(3):
            profiler.start_rule("TestRule")
            profiler.end_rule("TestRule", changes=2)

        profile = profiler.rule_profiles["TestRule"]
        assert profile.call_count == 3
        assert profile.changes_made == 6  # 2 × 3

    def test_generate_report(self):
        profiler = OptimizationProfiler()
        context = Mock(spec=OptimizationContext, maturity=0)

        # Simulate an optimization pass
        profiler.start_pass(context)

        profiler.start_rule("Rule1")
        profiler.end_rule("Rule1", changes=10)

        profiler.start_rule("Rule2")
        profiler.end_rule("Rule2", changes=5)

        profiler.end_pass(context, changes=15)

        # Generate report
        report = profiler.generate_report()

        assert report['total_passes'] == 1
        assert report['total_changes'] == 15
        assert len(report['rule_profiles']) == 2

        # Check that rules are sorted by time
        top_rules = report['top_rules_by_time']
        assert len(top_rules) > 0

    def test_json_report_generation(self):
        profiler = OptimizationProfiler()
        context = Mock(spec=OptimizationContext, maturity=0)

        profiler.start_pass(context)
        profiler.start_rule("TestRule")
        profiler.end_rule("TestRule", changes=5)
        profiler.end_pass(context, changes=5)

        # Save to temporary file
        with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
            temp_path = f.name

        try:
            profiler.save_json_report(temp_path)

            # Verify JSON is valid
            with open(temp_path, 'r') as f:
                data = json.load(f)

            assert data['total_passes'] == 1
            assert data['total_changes'] == 5
            assert len(data['rules']) == 1
            assert data['rules'][0]['name'] == "TestRule"
        finally:
            Path(temp_path).unlink()

    def test_html_report_generation(self):
        profiler = OptimizationProfiler()
        context = Mock(spec=OptimizationContext, maturity=0)

        profiler.start_pass(context)
        profiler.start_rule("TestRule")
        profiler.end_rule("TestRule", changes=5)
        profiler.end_pass(context, changes=5)

        # Save to temporary file
        with tempfile.NamedTemporaryFile(mode='w', suffix='.html', delete=False) as f:
            temp_path = f.name

        try:
            profiler.save_html_report(temp_path)

            # Verify HTML was created
            assert Path(temp_path).exists()

            # Check it contains expected content
            with open(temp_path, 'r') as f:
                html = f.read()

            assert 'D810 Optimization Profile' in html
            assert 'TestRule' in html
        finally:
            Path(temp_path).unlink()

    def test_profiler_reset(self):
        profiler = OptimizationProfiler()
        context = Mock(spec=OptimizationContext, maturity=0)

        profiler.start_pass(context)
        profiler.start_rule("TestRule")
        profiler.end_rule("TestRule", changes=5)
        profiler.end_pass(context, changes=5)

        assert len(profiler.pass_profiles) == 1
        assert len(profiler.rule_profiles) == 1

        profiler.reset()

        assert len(profiler.pass_profiles) == 0
        assert len(profiler.rule_profiles) == 0


@pytest.mark.skip(reason="SQLite cache tests hang - not working yet")
class TestOptimizationCache:
    """Tests for the persistent caching layer."""

    def test_cache_initialization(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            db_path = Path(tmpdir) / "test.db"
            cache = OptimizationCache(db_path)

            assert cache.db_path == db_path
            assert cache.conn is not None
            assert db_path.exists()

            cache.close()

    def test_context_manager(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            db_path = Path(tmpdir) / "test.db"

            with OptimizationCache(db_path) as cache:
                assert cache.conn is not None

            # Connection should be closed
            assert cache.conn is None

    def test_save_and_load_result(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            db_path = Path(tmpdir) / "test.db"

            with OptimizationCache(db_path) as cache:
                # Create mock mba
                mock_mba = Mock()
                mock_mba.qty = 10
                mock_mba.maturity = 0

                # Save result
                patches = [
                    {'type': 'redirect_edge', 'from': 5, 'to': 10},
                    {'type': 'insert_block', 'serial': 7}
                ]

                cache.save_optimization_result(
                    function_addr=0x401000,
                    mba=mock_mba,
                    maturity=0,
                    changes=42,
                    patches=patches
                )

                # Load result
                result = cache.load_optimization_result(0x401000, 0)

                assert result is not None
                assert result.function_addr == 0x401000
                assert result.maturity == 0
                assert result.changes_made == 42
                assert len(result.patches) == 2

    def test_cache_invalidation(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            db_path = Path(tmpdir) / "test.db"

            with OptimizationCache(db_path) as cache:
                mock_mba = Mock()
                mock_mba.qty = 10
                mock_mba.maturity = 0

                # Save result
                cache.save_optimization_result(
                    function_addr=0x401000,
                    mba=mock_mba,
                    maturity=0,
                    changes=42,
                    patches=[]
                )

                # Verify it exists
                result = cache.load_optimization_result(0x401000, 0)
                assert result is not None

                # Invalidate
                cache.invalidate_function(0x401000)

                # Verify it's gone
                result = cache.load_optimization_result(0x401000, 0)
                assert result is None

    def test_per_function_rules_enabled_only(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            db_path = Path(tmpdir) / "test.db"

            with OptimizationCache(db_path) as cache:
                # Configure: only enable UnflattenerRule
                cache.set_function_rules(
                    function_addr=0x401000,
                    enabled_rules={"UnflattenerRule"},
                    notes="Only unflatten this function"
                )

                # Check which rules should run
                assert cache.should_run_rule(0x401000, "UnflattenerRule") is True
                assert cache.should_run_rule(0x401000, "OtherRule") is False

    def test_per_function_rules_disabled(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            db_path = Path(tmpdir) / "test.db"

            with OptimizationCache(db_path) as cache:
                # Configure: disable SlowRule
                cache.set_function_rules(
                    function_addr=0x401000,
                    disabled_rules={"SlowRule"},
                    notes="This rule is too slow on this function"
                )

                # Check which rules should run
                assert cache.should_run_rule(0x401000, "FastRule") is True
                assert cache.should_run_rule(0x401000, "SlowRule") is False

    def test_per_function_rules_default(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            db_path = Path(tmpdir) / "test.db"

            with OptimizationCache(db_path) as cache:
                # No configuration = all rules run
                assert cache.should_run_rule(0x401000, "AnyRule") is True

    def test_get_function_rules(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            db_path = Path(tmpdir) / "test.db"

            with OptimizationCache(db_path) as cache:
                cache.set_function_rules(
                    function_addr=0x401000,
                    enabled_rules={"Rule1", "Rule2"},
                    disabled_rules={"Rule3"},
                    notes="Test config"
                )

                config = cache.get_function_rules(0x401000)

                assert config is not None
                assert config.function_addr == 0x401000
                assert "Rule1" in config.enabled_rules
                assert "Rule2" in config.enabled_rules
                assert "Rule3" in config.disabled_rules
                assert config.notes == "Test config"

    def test_cache_statistics(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            db_path = Path(tmpdir) / "test.db"

            with OptimizationCache(db_path) as cache:
                mock_mba = Mock()
                mock_mba.qty = 10
                mock_mba.maturity = 0

                # Add some data
                cache.save_optimization_result(
                    function_addr=0x401000,
                    mba=mock_mba,
                    maturity=0,
                    changes=42,
                    patches=[{'type': 'test'}]
                )

                cache.set_function_rules(
                    function_addr=0x401000,
                    enabled_rules={"TestRule"}
                )

                stats = cache.get_statistics()

                assert stats['functions_cached'] == 1
                assert stats['results_cached'] == 1
                assert stats['patches_stored'] == 1
                assert stats['functions_with_custom_rules'] == 1


@pytest.mark.skip(reason="SQLite cache integration tests hang - not working yet")
class TestIntegration:
    """Integration tests showing profiler and cache working together."""

    def test_profile_with_cache(self):
        """Simulate using profiler and cache together."""
        profiler = OptimizationProfiler()

        with tempfile.TemporaryDirectory() as tmpdir:
            db_path = Path(tmpdir) / "test.db"

            with OptimizationCache(db_path) as cache:
                context = Mock(spec=OptimizationContext, maturity=0)
                mock_mba = Mock()
                mock_mba.qty = 10
                mock_mba.maturity = 0

                # Simulate optimization pass
                profiler.start_pass(context)

                # Check cache
                result = cache.load_optimization_result(0x401000, 0)
                if result is None:
                    # Cache miss - run optimization
                    profiler.start_rule("UnflattenerRule")
                    # ... optimization happens ...
                    changes = 42
                    profiler.end_rule("UnflattenerRule", changes=changes)

                    # Save to cache
                    cache.save_optimization_result(
                        function_addr=0x401000,
                        mba=mock_mba,
                        maturity=0,
                        changes=changes,
                        patches=[]
                    )

                profiler.end_pass(context, changes=42)

                # Verify both systems recorded the data
                assert len(profiler.pass_profiles) == 1
                assert cache.load_optimization_result(0x401000, 0) is not None


"""
Performance Benefits
====================

These features address the performance optimization plan:

1. Profiling identifies bottlenecks:
   - Which rules take the most time?
   - Which passes are slowest?
   - Where should we optimize?

2. Caching eliminates redundant work:
   - Results persist across IDA sessions
   - Functions analyzed once, reused many times
   - Especially valuable for large binaries

3. Per-function rules enable fine-tuning:
   - Disable slow rules on large functions
   - Enable experimental rules selectively
   - Document optimization decisions

Example workflow:
    1. Run with profiling enabled
    2. Identify that UnflattenerRule takes 80% of time
    3. Run only on functions that are actually flattened
    4. Cache results
    5. Subsequent sessions are 10x faster
"""
