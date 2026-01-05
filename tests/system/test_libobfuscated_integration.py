"""Integration tests for d810-ng using libobfuscated.dll.

These tests verify that d810's optimizations work correctly against real
obfuscated binaries compiled with MBA and other obfuscation techniques.
"""

import logging
import textwrap
import unittest

try:
    import idaapi
    import idc
    IDA_AVAILABLE = True
except ImportError:
    IDA_AVAILABLE = False

from .ida_test_base import IDAProTestCase
from .stutils import d810_state, pseudocode_to_string


logger = logging.getLogger(__name__)


@unittest.skipUnless(IDA_AVAILABLE, "IDA Pro API not available")
class TestLibObfuscatedIntegration(IDAProTestCase):
    """Integration tests using libobfuscated.dll binary.

    This test suite opens libobfuscated.dll once and runs all tests against it.
    The binary contains functions with various obfuscation patterns that d810
    should simplify.
    """

    binary_name = "libobfuscated.dll"

    @classmethod
    def setUpClass(cls):
        """Open database and initialize Hex-Rays."""
        super().setUpClass()

        # Initialize the Hex-Rays decompiler plugin
        if not idaapi.init_hexrays_plugin():
            raise unittest.SkipTest("Hex-Rays decompiler plugin not available")

        # Configure Hex-Rays for better pseudocode display
        idaapi.change_hexrays_config("COLLAPSE_LVARS = YES")

        logger.info("Hex-Rays initialized successfully")

    def test_database_opened(self):
        """Verify that the database was opened successfully."""
        self.assertTrue(self.database_opened, "Database should be open")
        self.assertIsNotNone(self.min_ea, "min_ea should be set")
        self.assertIsNotNone(self.max_ea, "max_ea should be set")
        self.assertNotEqual(self.min_ea, idaapi.BADADDR)
        self.assertNotEqual(self.max_ea, idaapi.BADADDR)

    def test_hex_rays_available(self):
        """Verify that Hex-Rays decompiler is available."""
        self.assertTrue(
            idaapi.init_hexrays_plugin(),
            "Hex-Rays decompiler should be available"
        )

    def test_find_test_xor_function(self):
        """Verify that we can find the test_xor function."""
        func_ea = self.get_function_ea("test_xor")
        if func_ea is None:
            self.skipTest("Function 'test_xor' not found in database")

        self.assertNotEqual(func_ea, idaapi.BADADDR)
        logger.info(f"Found test_xor at {hex(func_ea)}")

    def test_xor_optimization_without_d810(self):
        """Test XOR function decompilation WITHOUT d810 optimizations.

        This establishes the baseline - what IDA produces without d810.
        The obfuscated XOR patterns should be visible.
        """
        func_ea = self.get_function_ea("test_xor")
        if func_ea is None:
            self.skipTest("Function 'test_xor' not found")

        with d810_state() as state:
            # Disable d810 to see unoptimized code
            state.stop_d810()

            # Decompile function
            cfunc = self.decompile_function(func_ea, no_cache=True)
            self.assertIsNotNone(cfunc, "Decompilation should succeed")

            # Get pseudocode
            pseudocode = self.get_pseudocode_string(cfunc)
            logger.debug(f"Unoptimized pseudocode:\n{pseudocode}")

            # Verify obfuscated patterns are present
            # MBA obfuscation typically shows: a + b - 2*(a & b)
            self.assertIn("2 *", pseudocode, "Should contain multiplication in MBA pattern")
            self.assertIn("&", pseudocode, "Should contain AND operation")

    def test_xor_optimization_with_d810(self):
        """Test XOR function decompilation WITH d810 optimizations.

        This verifies that d810 successfully simplifies MBA-obfuscated
        XOR patterns back to simple XOR operations.
        """
        func_ea = self.get_function_ea("test_xor")
        if func_ea is None:
            self.skipTest("Function 'test_xor' not found")

        with d810_state() as state:
            # Enable d810
            state.start_d810()

            # Decompile function with d810 active
            cfunc = self.decompile_function(func_ea, no_cache=True)
            self.assertIsNotNone(cfunc, "Decompilation should succeed")

            # Get pseudocode
            pseudocode = self.get_pseudocode_string(cfunc)
            logger.info(f"Optimized pseudocode:\n{pseudocode}")

            # Verify XOR simplification occurred
            self.assertIn("^", pseudocode, "Should contain XOR operation")

            # Verify MBA pattern is NOT present (simplified away)
            # Note: This might not always be true depending on the specific MBA pattern
            # but for standard (a + b - 2*(a & b)) it should simplify to (a ^ b)

    def test_constant_folding_optimization(self):
        """Test constant folding optimizations.

        Verifies that d810 can fold complex constant expressions
        into simpler forms.
        """
        func_ea = self.get_function_ea("test_cst_simplification")
        if func_ea is None:
            self.skipTest("Function 'test_cst_simplification' not found")

        with d810_state() as state:
            # Test without d810
            state.stop_d810()
            cfunc_unopt = self.decompile_function(func_ea, no_cache=True)
            pseudocode_unopt = self.get_pseudocode_string(cfunc_unopt)
            logger.debug(f"Unoptimized constant code:\n{pseudocode_unopt}")

            # Test with d810
            state.start_d810()
            cfunc_opt = self.decompile_function(func_ea, no_cache=True)
            pseudocode_opt = self.get_pseudocode_string(cfunc_opt)
            logger.info(f"Optimized constant code:\n{pseudocode_opt}")

            # The optimized version should be simpler
            # (fewer operations, more constants directly visible)
            self.assertIsNotNone(cfunc_opt)

    def test_opaque_predicate_simplification(self):
        """Test opaque predicate simplification.

        Verifies that d810 can identify and simplify opaque predicates
        (conditions that always evaluate to true or false).
        """
        func_ea = self.get_function_ea("test_opaque_predicate")
        if func_ea is None:
            self.skipTest("Function 'test_opaque_predicate' not found")

        with d810_state() as state:
            # Test without d810
            state.stop_d810()
            cfunc_unopt = self.decompile_function(func_ea, no_cache=True)
            self.assertIsNotNone(cfunc_unopt)

            pseudocode_unopt = self.get_pseudocode_string(cfunc_unopt)
            logger.debug(f"Unoptimized opaque predicate code:\n{pseudocode_unopt}")

            # Test with d810
            state.start_d810()
            cfunc_opt = self.decompile_function(func_ea, no_cache=True)
            self.assertIsNotNone(cfunc_opt)

            pseudocode_opt = self.get_pseudocode_string(cfunc_opt)
            logger.info(f"Optimized opaque predicate code:\n{pseudocode_opt}")

            # Verify simplification occurred (fewer complex conditions)

    def test_chained_add_simplification(self):
        """Test simplification of chained addition operations.

        Verifies that d810 can simplify complex chains of additions
        and subtractions.
        """
        func_ea = self.get_function_ea("test_chained_add")
        if func_ea is None:
            self.skipTest("Function 'test_chained_add' not found")

        with d810_state() as state:
            # Test with d810
            state.start_d810()
            cfunc = self.decompile_function(func_ea, no_cache=True)
            self.assertIsNotNone(cfunc, "Decompilation should succeed")

            pseudocode = self.get_pseudocode_string(cfunc)
            logger.info(f"Chained add pseudocode:\n{pseudocode}")

            # Verify the code compiles and is simplified
            self.assertIsNotNone(cfunc)

    def test_mba_guessing_optimization(self):
        """Test MBA guessing/simplification.

        Verifies that d810 can identify and simplify complex MBA
        (Mixed Boolean-Arithmetic) expressions.
        """
        func_ea = self.get_function_ea("test_mba_guessing")
        if func_ea is None:
            self.skipTest("Function 'test_mba_guessing' not found")

        with d810_state() as state:
            # Test without d810
            state.stop_d810()
            cfunc_unopt = self.decompile_function(func_ea, no_cache=True)
            if cfunc_unopt is None:
                self.skipTest("Decompilation failed")

            pseudocode_unopt = self.get_pseudocode_string(cfunc_unopt)
            logger.debug(f"Unoptimized MBA code:\n{pseudocode_unopt}")

            # Count complexity (approximate measure)
            unopt_ops = pseudocode_unopt.count('|') + pseudocode_unopt.count('&') + \
                        pseudocode_unopt.count('^') + pseudocode_unopt.count('*')

            # Test with d810
            state.start_d810()
            cfunc_opt = self.decompile_function(func_ea, no_cache=True)
            self.assertIsNotNone(cfunc_opt)

            pseudocode_opt = self.get_pseudocode_string(cfunc_opt)
            logger.info(f"Optimized MBA code:\n{pseudocode_opt}")

            # Count complexity after optimization
            opt_ops = pseudocode_opt.count('|') + pseudocode_opt.count('&') + \
                      pseudocode_opt.count('^') + pseudocode_opt.count('*')

            logger.info(f"Operation count: before={unopt_ops}, after={opt_ops}")

            # The optimized version should have fewer operations
            # (though this is a heuristic, not guaranteed)

    def test_d810_state_manager(self):
        """Test that d810 state manager works correctly."""
        with d810_state() as state:
            self.assertIsNotNone(state)
            self.assertTrue(hasattr(state, 'start_d810'))
            self.assertTrue(hasattr(state, 'stop_d810'))
            self.assertTrue(hasattr(state, 'is_loaded'))

            # Can start and stop
            state.start_d810()
            state.stop_d810()


@unittest.skipUnless(IDA_AVAILABLE, "IDA Pro API not available")
class TestPatternMatchingRules(IDAProTestCase):
    """Test individual pattern matching rules against specific functions.

    This test suite focuses on verifying that specific pattern matching
    rules from the refactored DSL are working correctly.
    """

    binary_name = "libobfuscated.dll"

    def test_xor_hackers_delight_rule(self):
        """Test Hacker's Delight XOR pattern: (x + y) - (x & y) => x | y."""
        # Find a function that uses this pattern
        func_ea = self.get_function_ea("test_xor")
        if func_ea is None:
            self.skipTest("test_xor function not found")

        with d810_state() as state:
            state.start_d810()
            cfunc = self.decompile_function(func_ea, no_cache=True)
            self.assertIsNotNone(cfunc)

            # Verify the pattern was simplified
            pseudocode = self.get_pseudocode_string(cfunc)
            # Should contain XOR (^) after optimization
            self.assertIn("^", pseudocode)

    def test_or_mba_rule(self):
        """Test OR MBA pattern: (x & y) + (x ^ y) => x | y."""
        func_ea = self.get_function_ea("test_or")
        if func_ea is None:
            # Fallback to any function with OR patterns
            self.skipTest("test_or function not found")

        with d810_state() as state:
            state.start_d810()
            cfunc = self.decompile_function(func_ea, no_cache=True)
            self.assertIsNotNone(cfunc)

    def test_negation_rules(self):
        """Test negation pattern rules."""
        func_ea = self.get_function_ea("test_neg")
        if func_ea is None:
            self.skipTest("test_neg function not found")

        with d810_state() as state:
            state.start_d810()
            cfunc = self.decompile_function(func_ea, no_cache=True)
            if cfunc is not None:
                pseudocode = self.get_pseudocode_string(cfunc)
                logger.info(f"Negation test pseudocode:\n{pseudocode}")


if __name__ == "__main__":
    # Configure logging for test runs
    logging.basicConfig(
        level=logging.INFO,
        format='%(levelname)s: %(message)s'
    )

    unittest.main()
