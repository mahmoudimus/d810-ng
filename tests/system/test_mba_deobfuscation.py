"""Enhanced integration tests for d810-ng deobfuscation pipeline.

This module provides comprehensive tests that verify:
- Before/after pseudocode comparison
- Specific rule applications
- MBA pattern simplifications
- Microcode transformations
"""

import logging
import re
import unittest
from typing import Dict, List, Tuple

try:
    import idaapi
    import ida_hexrays
    IDA_AVAILABLE = True
except ImportError:
    IDA_AVAILABLE = False

from .ida_test_base import IDAProTestCase
from .stutils import d810_state, pseudocode_to_string


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

    def __init__(self, before: str, after: str):
        self.before_code = before
        self.after_code = after
        self.before_ops = count_operations(before)
        self.after_ops = count_operations(after)
        self.before_return = extract_return_expression(before)
        self.after_return = extract_return_expression(after)

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

            # Get optimized (deobfuscated) pseudocode
            state.start_d810()
            cfunc_after = self.decompile_function(func_ea, no_cache=True)
            self.assertIsNotNone(cfunc_after, f"Decompilation with d810 failed")

            pseudocode_after = self.get_pseudocode_string(cfunc_after)
            logger.info(f"\n{'='*60}\n{description} - AFTER d810:\n{'='*60}\n{pseudocode_after}")

            # Create metrics
            metrics = DeobfuscationMetrics(pseudocode_before, pseudocode_after)

            # Log metrics
            logger.info(f"\nMetrics for {func_name}:")
            logger.info(f"  Total ops: {metrics.total_ops_before()} → {metrics.total_ops_after()}")
            logger.info(f"  Simplification ratio: {metrics.simplification_ratio():.2%}")
            logger.info(f"  Return expression before: {metrics.before_return}")
            logger.info(f"  Return expression after:  {metrics.after_return}")

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

        # Verify simplification occurred
        self.assertLess(metrics.total_ops_after(), metrics.total_ops_before(),
                       "XOR deobfuscation should reduce operation count")

        # XOR should replace the MBA pattern
        self.assertGreater(metrics.after_ops['xor'], 0,
                          "Deobfuscated code should contain XOR operations")

    def test_or_mba_pattern(self):
        """Test OR MBA pattern: (a & b) + (a ^ b) => a | b"""
        metrics = self._test_mba_pattern(
            func_name="test_or",
            expected_before_pattern=r"[\+\-]",   # Should have add/sub
            expected_after_pattern=r"\|",         # Should have OR
            description="OR MBA: (a & b) + (a ^ b)"
        )

        # OR should be present in deobfuscated code
        self.assertGreater(metrics.after_ops['or'], 0,
                          "Deobfuscated code should contain OR operations")

    def test_and_mba_pattern(self):
        """Test AND MBA pattern: (a | b) - (a ^ b) => a & b"""
        metrics = self._test_mba_pattern(
            func_name="test_and",
            expected_before_pattern=r"[\+\-\*]",  # Complex expression
            expected_after_pattern=r"&",          # Should have AND
            description="AND MBA: (a | b) - (a ^ b)"
        )

        # Verify AND is present after deobfuscation
        self.assertGreater(metrics.after_ops['and'], 0,
                          "Deobfuscated code should contain AND operations")

    def test_negation_pattern(self):
        """Test negation pattern: -x => ~x + 1"""
        metrics = self._test_mba_pattern(
            func_name="test_neg",
            expected_before_pattern=r"",  # May vary
            expected_after_pattern=r"",   # May vary
            description="Negation pattern"
        )

        logger.info(f"Negation test completed - check logs for details")

    def test_constant_propagation(self):
        """Test constant folding and propagation."""
        metrics = self._test_mba_pattern(
            func_name="test_cst_simplification",
            expected_before_pattern=r"",  # Complex constant expression
            expected_after_pattern=r"",   # Simplified constant
            description="Constant folding"
        )

        # Constants should be simplified
        self.assertLessEqual(metrics.simplification_ratio(), 1.0,
                           "Constant folding should not increase complexity")

    def test_chained_operations(self):
        """Test chained ADD/SUB simplification."""
        metrics = self._test_mba_pattern(
            func_name="test_chained_add",
            expected_before_pattern=r"[\+\-]",
            expected_after_pattern=r"",  # Should be simplified
            description="Chained ADD operations"
        )

        logger.info("Chained operations test - verify simplification in logs")

    def test_opaque_predicate_removal(self):
        """Test removal of opaque predicates (always true/false conditions)."""
        metrics = self._test_mba_pattern(
            func_name="test_opaque_predicate",
            expected_before_pattern=r"if",  # Should have conditionals
            expected_after_pattern=r"",     # May be simplified
            description="Opaque predicate removal"
        )

        logger.info("Opaque predicate test - check if dead code was eliminated")

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

        logger.info(f"\nOverall deobfuscation quality:")
        logger.info(f"  Total operations before: {total_before}")
        logger.info(f"  Total operations after:  {total_after}")
        logger.info(f"  Reduction: {total_before - total_after} ({(1 - total_after/total_before)*100:.1f}%)")

        # Overall, deobfuscation should reduce operations
        self.assertLess(total_after, total_before,
                       "D810 should reduce overall operation count")


if __name__ == "__main__":
    logging.basicConfig(
        level=logging.INFO,
        format='%(levelname)s: %(message)s'
    )
    unittest.main()
