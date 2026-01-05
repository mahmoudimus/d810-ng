"""Demonstration of structural deobfuscation assertions.

This test file shows how to use the instrumentation system to make
precise, structural assertions about deobfuscation quality.

Instead of brittle string matching, we assert things like:
- "Unflattener rule fired exactly once"
- "Redirected at least 10 edges"
- "XOR pattern simplified 5+ times"
- "Switch cases reduced from 18 to 3"

This makes tests more robust and easier to understand.
"""

import logging
import unittest

import idaapi
import idc

from .ida_test_base import IDAProTestCase
from .stutils import (
    d810_state,
    get_current_deobfuscation_context,
    pseudocode_to_string,
    setup_libobfuscated_function_names,
    configure_hexrays_for_consistent_output,
)
from .deobfuscation_assertions import (
    assert_rule_fired,
    assert_minimum_changes,
    assert_pattern_simplified,
    assert_total_changes,
    assert_deobfuscation_improved_code,
    get_deobfuscation_summary,
)

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


class TestStructuralDeobfuscation(IDAProTestCase):
    """Structural deobfuscation tests using instrumentation.

    These tests demonstrate the new assertion style that checks
    deobfuscation quality structurally rather than via string matching.
    """

    binary_name = "libobfuscated.dll"

    @classmethod
    def setUpClass(cls):
        """Open database and initialize Hex-Rays."""
        super().setUpClass()

        if not idaapi.init_hexrays_plugin():
            raise unittest.SkipTest("Hex-Rays decompiler plugin not available")

        configure_hexrays_for_consistent_output()
        setup_libobfuscated_function_names()

        # Enable detailed logging
        logging.getLogger("d810").setLevel(logging.DEBUG)

    def test_xor_pattern_structural(self):
        """Test XOR pattern simplification using structural assertions."""
        func_name = "test_xor"
        func_ea = idc.get_name_ea_simple(func_name)
        self.assertNotEqual(func_ea, idaapi.BADADDR, f"Function '{func_name}' not found")

        with d810_state() as state:
            # BEFORE: Decompile without d810
            state.stop_d810()
            decompiled_before = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
            self.assertIsNotNone(decompiled_before)
            code_before = pseudocode_to_string(decompiled_before.get_pseudocode())

            # AFTER: Decompile with d810
            with state.for_project("example_libobfuscated.json"):
                state.start_d810()
                decompiled_after = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
                self.assertIsNotNone(decompiled_after)
                code_after = pseudocode_to_string(decompiled_after.get_pseudocode())

            # Get instrumentation context
            ctx = get_current_deobfuscation_context()
            self.assertIsNotNone(ctx, "DeobfuscationContext should be available")

            # Print summary for debugging
            logger.info("\n" + get_deobfuscation_summary(ctx))

            # STRUCTURAL ASSERTIONS
            # These are much more precise than string matching!

            # 1. Assert that deobfuscation actually happened
            assert_deobfuscation_improved_code(ctx)

            # 2. Assert that pattern matching rules fired
            # (We expect XOR, AND, OR pattern rules to fire on this function)
            self.assertGreater(
                len(ctx.pattern_rules_that_fired()),
                0,
                "At least one pattern matching rule should have fired"
            )

            # 3. Assert that XOR patterns were simplified
            # The test_xor function contains obfuscated XOR patterns
            # that should be detected and simplified
            assert_pattern_simplified(ctx, "xor", min_count=1)

            # 4. Assert total changes are reasonable
            # This function has obfuscated patterns that should be simplified
            assert_total_changes(ctx, min_changes=1)

            # 5. Verify code actually changed
            self.assertNotEqual(
                code_before,
                code_after,
                "Code should be different after d810 optimization"
            )

            # 6. Verify simplified XOR operator appears in output
            self.assertIn("^", code_after, "Simplified XOR operator should appear")

    def test_constant_folding_structural(self):
        """Test constant folding using structural assertions."""
        func_name = "test_cst_simplification"
        func_ea = idc.get_name_ea_simple(func_name)
        self.assertNotEqual(func_ea, idaapi.BADADDR, f"Function '{func_name}' not found")

        with d810_state() as state:
            # BEFORE
            state.stop_d810()
            decompiled_before = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
            self.assertIsNotNone(decompiled_before)

            # AFTER
            state.start_d810()
            decompiled_after = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
            self.assertIsNotNone(decompiled_after)

            # Get context
            ctx = get_current_deobfuscation_context()
            logger.info("\n" + get_deobfuscation_summary(ctx))

            # STRUCTURAL ASSERTIONS

            # 1. Deobfuscation should have improved code
            assert_deobfuscation_improved_code(ctx)

            # 2. Constant folding patterns should have been simplified
            # (This test has many obfuscated constant expressions)
            assert_pattern_simplified(ctx, "constant", min_count=1)

            # 3. Total changes should be significant
            # Constant folding should make many changes
            assert_total_changes(ctx, min_changes=1)

    def test_mba_simplification_structural(self):
        """Test MBA pattern simplification using structural assertions."""
        func_name = "test_mba_guessing"
        func_ea = idc.get_name_ea_simple(func_name)
        self.assertNotEqual(func_ea, idaapi.BADADDR, f"Function '{func_name}' not found")

        with d810_state() as state:
            # BEFORE
            state.stop_d810()
            decompiled_before = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
            self.assertIsNotNone(decompiled_before)
            code_before = pseudocode_to_string(decompiled_before.get_pseudocode())

            # AFTER
            state.start_d810()
            decompiled_after = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
            self.assertIsNotNone(decompiled_after)
            code_after = pseudocode_to_string(decompiled_after.get_pseudocode())

            # Get context
            ctx = get_current_deobfuscation_context()
            logger.info("\n" + get_deobfuscation_summary(ctx))

            # STRUCTURAL ASSERTIONS

            # 1. Deobfuscation should improve code
            assert_deobfuscation_improved_code(ctx)

            # 2. MBA patterns should be simplified
            # This function has MBA (Mixed Boolean-Arithmetic) obfuscation
            # Our pattern rules should detect and simplify these
            # Note: MBA patterns may be matched as XOR, AND, OR patterns
            total_mba_related = (
                ctx.pattern_matches_by_type("mba") +
                ctx.pattern_matches_by_type("xor") +
                ctx.pattern_matches_by_type("and") +
                ctx.pattern_matches_by_type("or")
            )
            self.assertGreater(
                total_mba_related,
                0,
                "MBA-related patterns (XOR/AND/OR/MBA) should be simplified"
            )

            # 3. Code should have fewer operations after simplification
            ops_before = code_before.count('+') + code_before.count('-') + code_before.count('*')
            ops_after = code_after.count('+') + code_after.count('-') + code_after.count('*')
            self.assertLess(
                ops_after,
                ops_before,
                f"MBA simplification should reduce operators ({ops_before} → {ops_after})"
            )

    def test_opaque_predicate_removal_structural(self):
        """Test opaque predicate removal using structural assertions."""
        func_name = "test_opaque_predicate"
        func_ea = idc.get_name_ea_simple(func_name)
        self.assertNotEqual(func_ea, idaapi.BADADDR, f"Function '{func_name}' not found")

        with d810_state() as state:
            # BEFORE
            state.stop_d810()
            decompiled_before = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
            self.assertIsNotNone(decompiled_before)

            # AFTER
            state.start_d810()
            decompiled_after = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
            self.assertIsNotNone(decompiled_after)
            code_after = pseudocode_to_string(decompiled_after.get_pseudocode())

            # Get context
            ctx = get_current_deobfuscation_context()
            logger.info("\n" + get_deobfuscation_summary(ctx))

            # STRUCTURAL ASSERTIONS

            # 1. Deobfuscation should improve code
            assert_deobfuscation_improved_code(ctx)

            # 2. Pattern rules should fire
            # (Opaque predicates use MBA patterns that should be simplified)
            self.assertGreater(
                len(ctx.pattern_rules_that_fired()),
                0,
                "Pattern matching rules should fire on opaque predicates"
            )

            # 3. Constants should appear in output
            # After simplification, opaque predicates become constants (0 or 1)
            self.assertIn("= 1;", code_after, "Constant assignments should appear")
            self.assertIn("= 0;", code_after, "Constant assignments should appear")

    def test_instrumentation_provides_rule_details(self):
        """Test that instrumentation captures detailed rule information."""
        func_name = "test_xor"
        func_ea = idc.get_name_ea_simple(func_name)
        self.assertNotEqual(func_ea, idaapi.BADADDR)

        with d810_state() as state:
            with state.for_project("example_libobfuscated.json"):
                state.stop_d810()
                state.start_d810()

                # Decompile to trigger optimizations
                decompiled = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
                self.assertIsNotNone(decompiled)

            # Get context
            ctx = get_current_deobfuscation_context()

            # Verify context has detailed information
            self.assertIsNotNone(ctx, "Context should be available")
            self.assertGreater(len(ctx.executions), 0, "Should have execution records")

            # Check that we can query specific details
            summary = ctx.get_summary()
            self.assertIn("execution", summary)
            self.assertIn("rules", summary)
            self.assertIn("cfg", summary)
            self.assertIn("patterns", summary)

            # Verify we can query individual metrics
            total_changes = ctx.total_changes()
            self.assertIsInstance(total_changes, int)
            self.assertGreaterEqual(total_changes, 0)

            # Print detailed summary for manual inspection
            logger.info("\nDetailed Summary:")
            logger.info(f"  Total executions: {len(ctx.executions)}")
            logger.info(f"  Unique rules: {len(ctx.rules_fired)}")
            logger.info(f"  Total changes: {total_changes}")

            for rule_name in sorted(ctx.rules_fired.keys()):
                fire_count = ctx.rule_fire_count(rule_name)
                changes = ctx.total_changes_by_rule(rule_name)
                logger.info(f"  {rule_name}: {fire_count}x, {changes} changes")


if __name__ == "__main__":
    unittest.main()
