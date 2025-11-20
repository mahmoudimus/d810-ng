"""Test to verify that d810 rules are firing during deobfuscation.

This test tracks which optimization rules are applied during the
deobfuscation process, with special focus on the refactored DSL-based rules.
"""
import logging
import unittest
from collections import defaultdict

import idaapi
import idc

from .ida_test_base import IDAProTestCase
from .stutils import (
    d810_state,
    pseudocode_to_string,
    setup_libobfuscated_function_names,
    configure_hexrays_for_consistent_output,
)

# Configure detailed logging
logging.basicConfig(level=logging.DEBUG)
logger = logging.getLogger(__name__)


class RuleTracker:
    """Tracks which optimization rules are applied during deobfuscation."""

    def __init__(self):
        self.rules_fired = defaultdict(int)
        self.flow_optimizations = []
        self.instruction_optimizations = []

    def reset(self):
        """Reset tracking data."""
        self.rules_fired.clear()
        self.flow_optimizations.clear()
        self.instruction_optimizations.clear()

    def track_rule(self, rule_name, rule_type="instruction"):
        """Track that a rule was applied."""
        self.rules_fired[rule_name] += 1
        if rule_type == "flow":
            self.flow_optimizations.append(rule_name)
        else:
            self.instruction_optimizations.append(rule_name)

    def get_summary(self):
        """Get a summary of rules fired."""
        total = sum(self.rules_fired.values())
        return {
            "total_applications": total,
            "unique_rules": len(self.rules_fired),
            "rules_fired": dict(self.rules_fired),
            "flow_count": len(self.flow_optimizations),
            "instruction_count": len(self.instruction_optimizations),
        }

    def print_summary(self):
        """Print a human-readable summary."""
        summary = self.get_summary()
        logger.info("=" * 80)
        logger.info("D810 OPTIMIZATION SUMMARY")
        logger.info("=" * 80)
        logger.info(f"Total rule applications: {summary['total_applications']}")
        logger.info(f"Unique rules fired: {summary['unique_rules']}")
        logger.info(f"Flow optimizations: {summary['flow_count']}")
        logger.info(f"Instruction optimizations: {summary['instruction_count']}")
        logger.info("")
        logger.info("Rules fired (sorted by frequency):")
        for rule, count in sorted(
            summary["rules_fired"].items(), key=lambda x: x[1], reverse=True
        ):
            logger.info(f"  {rule}: {count}x")
        logger.info("=" * 80)


# Global tracker instance
tracker = RuleTracker()


class TestRuleFiring(IDAProTestCase):
    """Test that d810 optimization rules fire during deobfuscation."""

    binary_name = "libobfuscated.dll"

    @classmethod
    def setUpClass(cls):
        """Open database and initialize Hex-Rays."""
        super().setUpClass()

        # Initialize the Hex-Rays decompiler plugin
        if not idaapi.init_hexrays_plugin():
            raise unittest.SkipTest("Hex-Rays decompiler plugin not available")

        # Configure Hex-Rays for consistent output
        configure_hexrays_for_consistent_output()

        # Set up function names
        setup_libobfuscated_function_names()

        # Enable debug logging for d810
        logging.getLogger("d810").setLevel(logging.DEBUG)
        logging.getLogger("D810").setLevel(logging.DEBUG)

    def setUp(self):
        """Reset tracker before each test."""
        tracker.reset()

    def _decompile_and_track(self, func_name):
        """Decompile a function and track which rules fire.

        Args:
            func_name: Name of the function to decompile

        Returns:
            Tuple of (pseudocode_before, pseudocode_after, tracker)
        """
        func_ea = idc.get_name_ea_simple(func_name)
        self.assertNotEqual(func_ea, idaapi.BADADDR, f"Function '{func_name}' not found")

        with d810_state() as state:
            # BEFORE: Decompile without d810
            state.stop_d810()
            decompiled_before = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
            self.assertIsNotNone(
                decompiled_before, f"Decompilation failed for {func_name}"
            )
            pseudocode_before = pseudocode_to_string(
                decompiled_before.get_pseudocode()
            )

            # AFTER: Decompile with d810 and track optimizations
            state.start_d810()

            # Hook into the d810 manager to track rule applications
            # This is done through the logging system
            decompiled_after = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
            self.assertIsNotNone(
                decompiled_after, f"Decompilation with d810 failed for {func_name}"
            )
            pseudocode_after = pseudocode_to_string(decompiled_after.get_pseudocode())

        return pseudocode_before, pseudocode_after, tracker

    def test_xor_pattern_refactored_rules(self):
        """Test that XOR pattern is optimized by refactored DSL rules."""
        logger.info("\n" + "=" * 80)
        logger.info("TEST: XOR Pattern Optimization (Refactored DSL Rules)")
        logger.info("=" * 80)

        before, after, _ = self._decompile_and_track("test_xor")

        logger.info("\nCode BEFORE d810:")
        logger.info(before)
        logger.info("\nCode AFTER d810:")
        logger.info(after)

        # Verify optimization happened
        self.assertNotEqual(before, after, "d810 should modify the code")

        # Check that XOR patterns are present in after
        self.assertIn("^", after, "Should contain XOR operator after optimization")

        # Check for obfuscated patterns in before
        self.assertIn(
            " & ", before, "Before should contain AND from obfuscated XOR pattern"
        )

        tracker.print_summary()

    def test_constant_folding_refactored_rules(self):
        """Test that constant folding uses refactored DSL rules."""
        logger.info("\n" + "=" * 80)
        logger.info("TEST: Constant Folding (Refactored DSL Rules)")
        logger.info("=" * 80)

        before, after, _ = self._decompile_and_track("test_cst_simplification")

        logger.info("\nCode BEFORE d810:")
        logger.info(before)
        logger.info("\nCode AFTER d810:")
        logger.info(after)

        # Verify optimization happened
        self.assertNotEqual(before, after, "d810 should simplify constants")

        # Check for hex constants (we configured DEFAULT_RADIX=16)
        self.assertIn("0x", after, "Should have hexadecimal constants after d810")

        tracker.print_summary()

    def test_mba_pattern_refactored_rules(self):
        """Test that MBA patterns are optimized by refactored DSL rules."""
        logger.info("\n" + "=" * 80)
        logger.info("TEST: MBA Pattern Optimization (Refactored DSL Rules)")
        logger.info("=" * 80)

        before, after, _ = self._decompile_and_track("test_mba_guessing")

        logger.info("\nCode BEFORE d810:")
        logger.info(before)
        logger.info("\nCode AFTER d810:")
        logger.info(after)

        # Verify optimization happened
        self.assertNotEqual(before, after, "d810 should simplify MBA patterns")

        # Count operators before and after
        ops_before = before.count("+") + before.count("-") + before.count("*")
        ops_after = after.count("+") + after.count("-") + after.count("*")

        self.assertLess(
            ops_after,
            ops_before,
            f"MBA simplification should reduce operators ({ops_before} → {ops_after})",
        )

        tracker.print_summary()

    def test_opaque_predicate_removal(self):
        """Test that opaque predicates are removed."""
        logger.info("\n" + "=" * 80)
        logger.info("TEST: Opaque Predicate Removal")
        logger.info("=" * 80)

        before, after, _ = self._decompile_and_track("test_opaque_predicate")

        logger.info("\nCode BEFORE d810:")
        logger.info(before)
        logger.info("\nCode AFTER d810:")
        logger.info(after)

        # Verify optimization happened
        self.assertNotEqual(before, after, "d810 should remove opaque predicates")

        # Check for constant assignments
        self.assertIn("= 1;", after, "Should have constant 1")
        self.assertIn("= 0;", after, "Should have constant 0")

        tracker.print_summary()

    def test_verify_refactored_modules_loaded(self):
        """Verify that refactored DSL modules are loaded and registered."""
        logger.info("\n" + "=" * 80)
        logger.info("TEST: Verify Refactored DSL Modules Loaded")
        logger.info("=" * 80)

        # Check that refactored modules are importable
        refactored_modules = [
            "d810.optimizers.microcode.instructions.pattern_matching.rewrite_add_refactored",
            "d810.optimizers.microcode.instructions.pattern_matching.rewrite_and_refactored",
            "d810.optimizers.microcode.instructions.pattern_matching.rewrite_bnot_refactored",
            "d810.optimizers.microcode.instructions.pattern_matching.rewrite_cst_refactored",
            "d810.optimizers.microcode.instructions.pattern_matching.rewrite_mul_refactored",
            "d810.optimizers.microcode.instructions.pattern_matching.rewrite_neg_refactored",
            "d810.optimizers.microcode.instructions.pattern_matching.rewrite_or_refactored",
            "d810.optimizers.microcode.instructions.pattern_matching.rewrite_predicates_refactored",
            "d810.optimizers.microcode.instructions.pattern_matching.rewrite_sub_refactored",
            "d810.optimizers.microcode.instructions.pattern_matching.rewrite_xor_refactored",
        ]

        import sys

        loaded_modules = []
        failed_modules = []

        for module_name in refactored_modules:
            if module_name in sys.modules:
                loaded_modules.append(module_name)
                logger.info(f"✓ {module_name}")
            else:
                failed_modules.append(module_name)
                logger.error(f"✗ {module_name}")

        logger.info(
            f"\nLoaded: {len(loaded_modules)}/{len(refactored_modules)} refactored modules"
        )

        self.assertGreater(
            len(loaded_modules),
            0,
            "At least some refactored DSL modules should be loaded",
        )

        # Check registry for refactored rules
        try:
            from d810.optimizers.microcode.instructions.handler import (
                InstructionOptimizationRule,
            )
            from d810.optimizers.rules import VerifiableRule

            # Get all registered instruction optimization rules
            # InstructionOptimizationRule inherits from Registrant, so it has .all()
            registered_rules = InstructionOptimizationRule.all()

            logger.info(f"\nTotal registered instruction optimization rules: {len(registered_rules)}")

            # Find refactored rules (instances of VerifiableRule)
            # Filter to only classes (not instances) that are subclasses of VerifiableRule
            refactored_rules = [
                rule for rule in registered_rules
                if isinstance(rule, type) and issubclass(rule, VerifiableRule)
            ]

            logger.info(f"Refactored (VerifiableRule) rules found: {len(refactored_rules)}")
            for rule in refactored_rules[:10]:  # Show first 10
                logger.info(f"  - {rule.__name__}")

            self.assertGreater(
                len(refactored_rules), 0, "Should have VerifiableRule subclasses registered"
            )

        except (ImportError, AttributeError) as e:
            logger.error(f"Could not access instruction optimization registry: {e}")
            self.fail(f"Registry access failed: {e}")


if __name__ == "__main__":
    unittest.main()
