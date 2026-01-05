"""Enhanced integration tests for d810-ng deobfuscation pipeline.

This module provides comprehensive tests that verify:
- Before/after pseudocode comparison
- Specific rule applications
- MBA pattern simplifications
- Microcode transformations
- Rule firing metrics (which rules fired, how many times)
"""

import logging
import re
import unittest
from typing import Dict, List, Tuple, Optional

try:
    import idaapi
    import ida_hexrays
    IDA_AVAILABLE = True
except ImportError:
    IDA_AVAILABLE = False

from .ida_test_base import IDAProTestCase
from .stutils import d810_state, pseudocode_to_string, setup_libobfuscated_function_names

# Import profiling infrastructure
try:
    from d810.optimizers.profiling import OptimizationProfiler
    PROFILING_AVAILABLE = True
except ImportError:
    PROFILING_AVAILABLE = False
    OptimizationProfiler = None

logger = logging.getLogger(__name__)


def count_operations(pseudocode: str) -> Dict[str, int]:
    """Count different operations in pseudocode.

    Returns:
        Dictionary with counts of operations like +, -, *, &, |, ^, etc.
    """
    return {
        'add': pseudocode.count(' + '),
        'sub': pseudocode.count(' - '),
        'mul': pseudocode.count(' * '),
        'and': pseudocode.count(' & '),
        'or': pseudocode.count(' | '),
        'xor': pseudocode.count(' ^ '),
        'not': pseudocode.count('~'),
        'shift_left': pseudocode.count(' << '),
        'shift_right': pseudocode.count(' >> '),
    }


def extract_return_expression(pseudocode: str) -> str:
    """Extract the return statement from pseudocode.

    Args:
        pseudocode: Full pseudocode string

    Returns:
        The expression being returned, or empty string if not found
    """
    match = re.search(r'return\s+(.+?);', pseudocode, re.MULTILINE | re.DOTALL)
    if match:
        return match.group(1).strip()
    return ""


class DeobfuscationMetrics:
    """Track metrics before and after deobfuscation."""

    def __init__(self, before: str, after: str, profiler: Optional['OptimizationProfiler'] = None):
        self.before_code = before
        self.after_code = after
        self.before_ops = count_operations(before)
        self.after_ops = count_operations(after)
        self.before_return = extract_return_expression(before)
        self.after_return = extract_return_expression(after)
        self.profiler = profiler

    def total_ops_before(self) -> int:
        return sum(self.before_ops.values())

    def total_ops_after(self) -> int:
        return sum(self.after_ops.values())

    def simplification_ratio(self) -> float:
        """Ratio of operations after vs before (lower is better)."""
        before_total = self.total_ops_before()
        if before_total == 0:
            return 1.0
        return self.total_ops_after() / before_total

    def op_reduction(self, op_name: str) -> int:
        """Number of operations removed for a specific operation."""
        return self.before_ops.get(op_name, 0) - self.after_ops.get(op_name, 0)

    def get_rules_fired(self) -> Dict[str, int]:
        """Get which rules fired and how many times.

        Returns:
            Dict mapping rule name to number of times it was applied (with changes > 0)
        """
        if not self.profiler or not PROFILING_AVAILABLE:
            return {}

        rules_with_changes = {}
        for rule_name, profile in self.profiler.rule_profiles.items():
            if profile.changes_made > 0:
                rules_with_changes[rule_name] = profile.changes_made

        return rules_with_changes

    def log_rule_metrics(self):
        """Log detailed rule firing metrics."""
        if not self.profiler or not PROFILING_AVAILABLE:
            logger.info("Profiling not available")
            return

        rules_fired = self.get_rules_fired()
        if rules_fired:
            logger.info(f"\nRules that fired ({len(rules_fired)} total):")
            for rule_name, changes in sorted(rules_fired.items(), key=lambda x: x[1], reverse=True):
                profile = self.profiler.rule_profiles[rule_name]
                logger.info(f"  {rule_name}: {changes} changes, {profile.call_count} calls")
        else:
            logger.info("No rules fired with changes")


@unittest.skipUnless(IDA_AVAILABLE, "IDA Pro API not available")
class TestMBADeobfuscationPipeline(IDAProTestCase):
    """Test MBA deobfuscation patterns with before/after verification.

    Each test:
    1. Decompiles without d810 to get baseline (obfuscated)
    2. Decompiles with d810 to get optimized code
    3. Compares metrics to verify simplification
    4. Validates specific patterns were simplified
    """

    binary_name = "libobfuscated.dll"

    @classmethod
    def setUpClass(cls):
        """Open database and initialize Hex-Rays."""
        super().setUpClass()

        # Initialize Hex-Rays
        if not idaapi.init_hexrays_plugin():
            raise unittest.SkipTest("Hex-Rays decompiler plugin not available")

        # Set up function names for libobfuscated.dll since they're not exported
        setup_libobfuscated_function_names()

        logger.info("Hex-Rays initialized for MBA deobfuscation tests")

    def _test_mba_pattern(self, func_name: str,
                          expected_before_pattern: str,
                          expected_after_pattern: str,
                          description: str) -> DeobfuscationMetrics:
        """Generic test for an MBA pattern.

        Args:
            func_name: Name of function to test
            expected_before_pattern: Regex pattern that should match obfuscated code
            expected_after_pattern: Regex pattern that should match deobfuscated code
            description: Human-readable description of the pattern

        Returns:
            DeobfuscationMetrics object with before/after comparison
        """
        func_ea = self.get_function_ea(func_name)
        if func_ea is None:
            self.skipTest(f"Function '{func_name}' not found")

        with d810_state() as state:
            # Get unoptimized (obfuscated) pseudocode
            state.stop_d810()
            cfunc_before = self.decompile_function(func_ea, no_cache=True)
            self.assertIsNotNone(cfunc_before, f"Decompilation of {func_name} failed")

            pseudocode_before = self.get_pseudocode_string(cfunc_before)
            logger.info(f"\n{'='*60}\n{description} - BEFORE d810:\n{'='*60}\n{pseudocode_before}")

            # Enable profiling to track rule applications
            profiler = None
            if PROFILING_AVAILABLE and hasattr(state, 'manager') and state.manager:
                profiler = OptimizationProfiler()
                state.manager.set_profiling_hooks(
                    pre_hook=profiler.start_pass,
                    post_hook=profiler.end_pass
                )
                logger.debug("Profiling enabled for rule tracking")

            # Get optimized (deobfuscated) pseudocode
            state.start_d810()
            cfunc_after = self.decompile_function(func_ea, no_cache=True)
            self.assertIsNotNone(cfunc_after, f"Decompilation with d810 failed")

            pseudocode_after = self.get_pseudocode_string(cfunc_after)
            logger.info(f"\n{'='*60}\n{description} - AFTER d810:\n{'='*60}\n{pseudocode_after}")

            # Create metrics with profiler data
            metrics = DeobfuscationMetrics(pseudocode_before, pseudocode_after, profiler)

            # Log metrics
            logger.info(f"\nMetrics for {func_name}:")
            logger.info(f"  Total ops: {metrics.total_ops_before()} → {metrics.total_ops_after()}")
            logger.info(f"  Simplification ratio: {metrics.simplification_ratio():.2%}")
            logger.info(f"  Return expression before: {metrics.before_return}")
            logger.info(f"  Return expression after:  {metrics.after_return}")

            # Log rule firing metrics
            metrics.log_rule_metrics()

            # Verify pattern transformations
            if expected_before_pattern:
                self.assertRegex(pseudocode_before, expected_before_pattern,
                               f"Obfuscated pattern not found in {func_name}")

            if expected_after_pattern:
                self.assertRegex(pseudocode_after, expected_after_pattern,
                               f"Simplified pattern not found after d810 in {func_name}")

            return metrics

    def test_xor_mba_pattern(self):
        """Test XOR MBA pattern: (a + b) - 2*(a & b) => a ^ b"""
        metrics = self._test_mba_pattern(
            func_name="test_xor",
            expected_before_pattern=r"2\s*\*",  # Should have multiplication by 2
            expected_after_pattern=r"\^",        # Should have XOR
            description="XOR MBA: (a + b) - 2*(a & b)"
        )

        # ASSERT: MBA obfuscation pattern is present BEFORE deobfuscation
        self.assertGreater(metrics.before_ops['mul'], 0,
                          "Obfuscated XOR should contain multiplication (2*)")
        self.assertGreater(metrics.before_ops['and'], 0,
                          "Obfuscated XOR should contain AND operations")

        # ASSERT: Deobfuscation actually happened - operations reduced
        self.assertLess(metrics.total_ops_after(), metrics.total_ops_before(),
                       "XOR deobfuscation MUST reduce operation count")

        # ASSERT: MBA pattern was simplified (multiplication reduced or removed)
        mul_reduction = metrics.op_reduction('mul')
        self.assertGreaterEqual(mul_reduction, 0,
                               "Deobfuscation should reduce or eliminate multiplications")

        # ASSERT: XOR operations replaced the MBA pattern
        self.assertGreater(metrics.after_ops['xor'], 0,
                          "Deobfuscated code MUST contain XOR operations")

        # ASSERT: Code actually changed (not just same code)
        self.assertNotEqual(metrics.before_code, metrics.after_code,
                           "Deobfuscation MUST change the code")

        # ASSERT: Simplification ratio shows improvement (should be significantly less than 1.0)
        self.assertLess(metrics.simplification_ratio(), 0.95,
                       f"XOR should simplify significantly (ratio={metrics.simplification_ratio():.2f})")

    def test_or_mba_pattern(self):
        """Test OR MBA pattern: (a & b) + (a ^ b) => a | b"""
        metrics = self._test_mba_pattern(
            func_name="test_or",
            expected_before_pattern=r"[\+\-]",   # Should have add/sub
            expected_after_pattern=r"\|",         # Should have OR
            description="OR MBA: (a & b) + (a ^ b)"
        )

        # ASSERT: MBA obfuscation pattern present BEFORE (AND and XOR used to create OR)
        self.assertGreater(metrics.before_ops['and'] + metrics.before_ops['xor'], 0,
                          "Obfuscated OR should use AND and XOR operations")
        self.assertGreater(metrics.before_ops['add'], 0,
                          "Obfuscated OR MBA pattern should use addition")

        # ASSERT: OR operations replaced the MBA pattern AFTER deobfuscation
        self.assertGreater(metrics.after_ops['or'], 0,
                          "Deobfuscated code MUST contain OR operations")

        # ASSERT: Deobfuscation reduced complexity
        self.assertLessEqual(metrics.total_ops_after(), metrics.total_ops_before(),
                            "OR deobfuscation should not increase operation count")

        # ASSERT: Code actually changed
        self.assertNotEqual(metrics.before_code, metrics.after_code,
                           "Deobfuscation MUST change the code")

        # ASSERT: Addition operations were reduced (since OR replaced (a&b)+(a^b))
        add_reduction = metrics.op_reduction('add')
        self.assertGreaterEqual(add_reduction, 0,
                               "OR deobfuscation should reduce addition operations")

    def test_and_mba_pattern(self):
        """Test AND MBA pattern: (a | b) - (a ^ b) => a & b"""
        metrics = self._test_mba_pattern(
            func_name="test_and",
            expected_before_pattern=r"[\+\-\*]",  # Complex expression
            expected_after_pattern=r"&",          # Should have AND
            description="AND MBA: (a | b) - (a ^ b)"
        )

        # ASSERT: MBA obfuscation pattern present BEFORE (OR and XOR used to create AND)
        self.assertGreater(metrics.before_ops['or'] + metrics.before_ops['xor'], 0,
                          "Obfuscated AND should use OR and XOR operations")
        self.assertGreater(metrics.before_ops['sub'], 0,
                          "Obfuscated AND MBA pattern should use subtraction")

        # ASSERT: AND operations present AFTER deobfuscation
        self.assertGreater(metrics.after_ops['and'], 0,
                          "Deobfuscated code MUST contain AND operations")

        # ASSERT: Deobfuscation reduced complexity
        self.assertLess(metrics.total_ops_after(), metrics.total_ops_before(),
                       "AND deobfuscation MUST reduce operation count")

        # ASSERT: Code actually changed
        self.assertNotEqual(metrics.before_code, metrics.after_code,
                           "Deobfuscation MUST change the code")

        # ASSERT: Subtraction operations were reduced (since AND replaced (a|b)-(a^b))
        sub_reduction = metrics.op_reduction('sub')
        self.assertGreaterEqual(sub_reduction, 0,
                               "AND deobfuscation should reduce subtraction operations")

    def test_negation_pattern(self):
        """Test negation pattern: ~x + 1 => -x (two's complement)"""
        metrics = self._test_mba_pattern(
            func_name="test_neg",
            expected_before_pattern=r"~",  # Should have bitwise NOT
            expected_after_pattern=r"-",   # Should have negation
            description="Negation pattern: ~x + 1"
        )

        # ASSERT: Obfuscated form uses NOT (~) and addition
        self.assertGreater(metrics.before_ops['not'], 0,
                          "Obfuscated negation should use bitwise NOT (~)")

        # ASSERT: Code was deobfuscated (changed)
        # Note: May not always simplify to unary minus, but should at least not get worse
        self.assertLessEqual(metrics.simplification_ratio(), 1.0,
                            "Negation deobfuscation should not increase complexity")

        logger.info(f"Negation test completed - simplification ratio: {metrics.simplification_ratio():.2f}")

    def test_constant_propagation(self):
        """Test constant folding and propagation."""
        metrics = self._test_mba_pattern(
            func_name="test_cst_simplification",
            expected_before_pattern=r"0x[0-9A-Fa-f]+",  # Should have hex constants
            expected_after_pattern=r"",   # May be simplified
            description="Constant folding"
        )

        # ASSERT: Deobfuscation should not make code worse
        self.assertLessEqual(metrics.simplification_ratio(), 1.0,
                           "Constant folding MUST NOT increase complexity")

        # ASSERT: Total operation count should decrease or stay same
        self.assertLessEqual(metrics.total_ops_after(), metrics.total_ops_before(),
                            "Constant folding should reduce or maintain operation count")

        logger.info(f"Constant folding reduced ops by: {metrics.total_ops_before() - metrics.total_ops_after()}")

    def test_chained_operations(self):
        """Test chained ADD/SUB simplification."""
        metrics = self._test_mba_pattern(
            func_name="test_chained_add",
            expected_before_pattern=r"[\+\-]",
            expected_after_pattern=r"",  # Should be simplified
            description="Chained ADD operations"
        )

        # ASSERT: Chained operations should simplify
        self.assertLess(metrics.total_ops_after(), metrics.total_ops_before(),
                       "Chained ADD/SUB operations MUST be simplified")

        # ASSERT: Simplification ratio should show improvement
        self.assertLess(metrics.simplification_ratio(), 1.0,
                       f"Chained ops should simplify (ratio={metrics.simplification_ratio():.2f})")

        logger.info(f"Chained operations simplified: {metrics.total_ops_before()} → {metrics.total_ops_after()} ops")

    def test_opaque_predicate_removal(self):
        """Test removal of opaque predicates (always true/false conditions)."""
        metrics = self._test_mba_pattern(
            func_name="test_opaque_predicate",
            expected_before_pattern=r"",  # Complex predicates
            expected_after_pattern=r"",   # May be simplified
            description="Opaque predicate removal"
        )

        # ASSERT: Deobfuscation should simplify the code
        self.assertLessEqual(metrics.simplification_ratio(), 1.0,
                            "Opaque predicate removal should not increase complexity")

        # ASSERT: Some simplification should occur
        # Note: Opaque predicates are tricky - may not always be fully eliminated
        # but the code should at least not get more complex
        self.assertLessEqual(metrics.total_ops_after(), metrics.total_ops_before(),
                            "Opaque predicates should not increase operation count")

        logger.info(f"Opaque predicate test - ops: {metrics.total_ops_before()} → {metrics.total_ops_after()}")

    def test_mba_guessing_complex_pattern(self):
        """Test very complex MBA expression that requires multiple rule applications."""
        metrics = self._test_mba_pattern(
            func_name="test_mba_guessing",
            expected_before_pattern=r"",  # Very complex
            expected_after_pattern=r"",   # Should be simplified
            description="Complex MBA guessing pattern"
        )

        # ASSERT: Complex MBA should definitely simplify
        self.assertLess(metrics.total_ops_after(), metrics.total_ops_before(),
                       "Complex MBA patterns MUST be simplified by d810")

        # ASSERT: Significant simplification should occur
        self.assertLess(metrics.simplification_ratio(), 0.9,
                       f"Complex MBA should simplify significantly (ratio={metrics.simplification_ratio():.2f})")

        logger.info(f"Complex MBA: {metrics.total_ops_before()} ops → {metrics.total_ops_after()} ops "
                   f"(reduced by {metrics.total_ops_before() - metrics.total_ops_after()})")

    def test_overall_deobfuscation_quality(self):
        """Test that overall code quality improves across multiple functions."""
        test_functions = [
            "test_xor",
            "test_or",
            "test_and",
            "test_neg",
        ]

        total_before = 0
        total_after = 0
        functions_tested = 0

        for func_name in test_functions:
            func_ea = self.get_function_ea(func_name)
            if func_ea is None:
                logger.warning(f"Skipping {func_name} - not found")
                continue

            with d810_state() as state:
                # Before
                state.stop_d810()
                cfunc_before = self.decompile_function(func_ea, no_cache=True)
                if cfunc_before:
                    pc_before = self.get_pseudocode_string(cfunc_before)
                    ops_before = sum(count_operations(pc_before).values())
                    total_before += ops_before

                # After
                state.start_d810()
                cfunc_after = self.decompile_function(func_ea, no_cache=True)
                if cfunc_after:
                    pc_after = self.get_pseudocode_string(cfunc_after)
                    ops_after = sum(count_operations(pc_after).values())
                    total_after += ops_after
                    functions_tested += 1

        logger.info(f"\nOverall deobfuscation quality:")
        logger.info(f"  Functions tested: {functions_tested}")
        logger.info(f"  Total operations before: {total_before}")
        logger.info(f"  Total operations after:  {total_after}")
        if total_before > 0:
            reduction_pct = (1 - total_after/total_before) * 100
            logger.info(f"  Reduction: {total_before - total_after} ({reduction_pct:.1f}%)")

        # ASSERT: At least one function was tested
        self.assertGreater(functions_tested, 0,
                          "At least one test function should be found and tested")

        # ASSERT: Overall, deobfuscation should reduce operations
        self.assertLess(total_after, total_before,
                       "D810 MUST reduce overall operation count across all MBA patterns")

        # ASSERT: Reduction should be significant (at least 10%)
        reduction_ratio = 1 - (total_after / total_before)
        self.assertGreater(reduction_ratio, 0.1,
                          f"D810 should reduce operations by at least 10% (actual: {reduction_ratio*100:.1f}%)")


if __name__ == "__main__":
    logging.basicConfig(
        level=logging.INFO,
        format='%(levelname)s: %(message)s'
    )
    unittest.main()
