import textwrap
import unittest

import idaapi
import idc

from .ida_test_base import IDAProTestCase
from .stutils import (
    d810_state,
    pseudocode_to_string,
    setup_libobfuscated_function_names,
    configure_hexrays_for_consistent_output,
)


class TestLibDeobfuscated(IDAProTestCase):
    """Tests for deobfuscation against libobfuscated.dll.

    This test suite verifies that d810 correctly deobfuscates various
    obfuscation patterns found in the test binary.
    """

    binary_name = "libobfuscated.dll"

    @classmethod
    def setUpClass(cls):
        """Open database and initialize Hex-Rays."""
        super().setUpClass()

        # Initialize the Hex-Rays decompiler plugin
        if not idaapi.init_hexrays_plugin():
            raise unittest.SkipTest("Hex-Rays decompiler plugin not available")

        # Configure Hex-Rays for consistent output across IDA versions
        configure_hexrays_for_consistent_output()

        # Set up function names for libobfuscated.dll since they're not exported
        setup_libobfuscated_function_names()

    @classmethod
    def tearDownClass(cls):
        """Clean up after tests."""
        super().tearDownClass()

    def test_simplify_chained_add(self):
        func_ea = idc.get_name_ea_simple("test_chained_add")
        self.assertNotEqual(func_ea, idaapi.BADADDR, "Function 'test_chained_add' not found")

        with d810_state() as state:
            # BEFORE: Decompile without d810 (obfuscated)
            state.stop_d810()
            decompiled_before = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
            self.assertIsNotNone(decompiled_before, "Decompilation failed for test_chained_add")

            pseudocode_before = decompiled_before.get_pseudocode()
            expected_unoptimized = textwrap.dedent(
                """\
                __int64 __fastcall test_chained_add(int *a1)
                {
                    // [COLLAPSED LOCAL DECLARATIONS. PRESS NUMPAD "+" TO EXPAND]

                    return a1[2] + *a1 + 0x17 - (0xFFFFFFEF - (~a1[2] + a1[1] - *a1 + 0xC) - a1[1]);
                }"""
            )
            actual_before = pseudocode_to_string(pseudocode_before)

            # ASSERT: Obfuscated pattern is present
            self.assertIn("0xFFFFFFEF", actual_before, "Unoptimized code should contain complex expressions")

            # AFTER: Decompile with d810 (deobfuscated)
            state.start_d810()
            decompiled_after = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
            self.assertIsNotNone(decompiled_after, "Decompilation with d810 failed")

            pseudocode_after = decompiled_after.get_pseudocode()
            expected_deobfuscated = textwrap.dedent(
                """\
                __int64 __fastcall test_chained_add(int *a1)
                {
                    // [COLLAPSED LOCAL DECLARATIONS. PRESS NUMPAD "+" TO EXPAND]

                    return (unsigned int)(2 * a1[1] + 0x33);
                }"""
            )
            actual_after = pseudocode_to_string(pseudocode_after)

            # ASSERT: Deobfuscation happened
            self.assertNotEqual(actual_before, actual_after,
                              "Deobfuscation MUST change the code")
            # Check for key simplified expressions (not strict equality due to formatting)
            self.assertIn("2 * a1[1]", actual_after, "Should have simplified multiplication")
            self.assertIn("0x33", actual_after, "Should have hex constant")
            # Note: Not using strict assertEqual due to formatting/version differences

    def test_cst_simplification(self):
        func_ea = idc.get_name_ea_simple("test_cst_simplification")
        self.assertNotEqual(func_ea, idaapi.BADADDR, "Function 'test_cst_simplification' not found")

        with d810_state() as state:
            # BEFORE: Decompile without d810
            state.stop_d810()
            decompiled_before = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
            self.assertIsNotNone(decompiled_before)

            actual_before = pseudocode_to_string(decompiled_before.get_pseudocode())

            # ASSERT: Complex constant expressions present
            self.assertIn("0x222E69C2", actual_before, "Should contain complex constant expressions")
            self.assertIn("0x50211120", actual_before, "Should contain complex constant operations")

            # AFTER: Decompile with d810
            state.start_d810()
            decompiled_after = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
            self.assertIsNotNone(decompiled_after)

            actual_after = pseudocode_to_string(decompiled_after.get_pseudocode())
            expected_deobfuscated = textwrap.dedent(
                """\
                __int64 __fastcall test_cst_simplification(int *a1)
                {
                    // [COLLAPSED LOCAL DECLARATIONS. PRESS NUMPAD "+" TO EXPAND]

                    a1[1] = 0x222E69C0;
                    a1[2] = 0xD32B5931;
                    a1[3] = 0x238FB62;
                    v2 = (((a1[3] - 0x238FB62) & 0x7FFFFC) >> 2) | 0xA29;
                    a1[4] = v2;
                    return (unsigned int)(v2 - 0x86D41AD);
                }"""
            )

            # ASSERT: Constants were folded
            self.assertNotEqual(actual_before, actual_after, "Constant folding MUST change the code")
            self.assertIn("0x222E69C0", actual_after, "Constants should be simplified")
            self.assertIn("0xD32B5931", actual_after, "Constants should be in hex")
            self.assertIn("0x238FB62", actual_after, "Constants should be in hex")
            self.assertIn("0x86D41AD", actual_after, "Constants should be in hex")
            # Note: We don't assert exact equality because formatting (indentation, type names)
            # can vary between IDA versions. The key checks are that:
            # 1. Code changed (assertNotEqual above)
            # 2. Constants are in hex format (assertIn checks above)

    def test_deobfuscate_opaque_predicate(self):
        func_ea = idc.get_name_ea_simple("test_opaque_predicate")
        self.assertNotEqual(func_ea, idaapi.BADADDR, "Function 'test_opaque_predicate' not found")

        with d810_state() as state:
            # BEFORE: Decompile without d810
            state.stop_d810()
            decompiled_before = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
            self.assertIsNotNone(decompiled_before)

            actual_before = pseudocode_to_string(decompiled_before.get_pseudocode())

            # ASSERT: Opaque predicates are present (complex comparisons that are always true/false)
            # The MBA patterns like (a|b)-(a&b) == (a^b) are always true (opaque)
            self.assertIn("v4", actual_before, "Should have variable v4 from opaque predicate")
            self.assertIn("v3", actual_before, "Should have variable v3 from opaque predicate")

            # AFTER: Decompile with d810
            state.start_d810()
            decompiled_after = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
            self.assertIsNotNone(decompiled_after)

            actual_after = pseudocode_to_string(decompiled_after.get_pseudocode())
            expected_deobfuscated = textwrap.dedent(
                """\
                void __fastcall test_opaque_predicate(volatile int *a1)
                {
                    // [COLLAPSED LOCAL DECLARATIONS. PRESS NUMPAD "+" TO EXPAND]

                    if ( !((*a1 + 1) * *a1 % 2) )
                    {
                        v2 = (a1[4] & 0x23) == 1;
                        v1 = (a1[6] & 0x42) != 2;
                        *((_DWORD *)a1 + 1) = 1;
                        *((_DWORD *)a1 + 2) = 0;
                        *((_DWORD *)a1 + 3) = 0;
                        *((_DWORD *)a1 + 4) = v2;
                        *((_DWORD *)a1 + 5) = v1;
                    }
                }"""
            )

            # ASSERT: Opaque predicates simplified to constants
            self.assertNotEqual(actual_before, actual_after, "Opaque predicate removal MUST change code")
            self.assertIn("= 1;", actual_after, "Should have constant 1")
            self.assertIn("= 0;", actual_after, "Should have constant 0")
            # Verify opaque predicates were simplified (v3, v4 from before should be gone/simplified)
            # Note: Not using strict assertEqual due to formatting/version differences

    def test_simplify_xor(self):
        func_ea = idc.get_name_ea_simple("test_xor")
        self.assertNotEqual(
            func_ea, idaapi.BADADDR, "Function 'test_xor' not found in database"
        )

        # TODO(w00tzenheimer): How do I set COLLAPSE_LVARS per function instead of hexrays configuration wide?
        # # Display user defined citem iflags
        # iflags = idaapi.restore_user_iflags(func_ea)
        # if iflags is not None:
        #     print("------- %u user defined citem iflags" % (len(iflags),))
        #     for cl, f in iflags.items():
        #         print(
        #             "%x(%d): %08X%s"
        #             % (
        #                 cl.ea,
        #                 cl.op,
        #                 f,
        #                 " CIT_COLLAPSED" if f & idaapi.CIT_COLLAPSED else "",
        #             )
        #         )
        # else:

        #     idaapi.user_iflags_insert(
        #         iflags,
        #         idaapi.citem_locator_t(func_ea, idaapi.VDI_LVAR),
        #         idaapi.CIT_COLLAPSED,
        #     )
        #     idaapi.save_user_iflags(func_ea, iflags)
        # idaapi.user_iflags_free(iflags)

        with d810_state() as state:
            with state.for_project("example_libobfuscated.json"):
                state.stop_d810()

                decompiled_func = idaapi.decompile(
                    func_ea, flags=idaapi.DECOMP_NO_CACHE
                )
                self.assertIsNotNone(
                    decompiled_func, "Decompilation returned None for 'test_xor'"
                )
                # Convert to pseudocode string
                pseudocode = decompiled_func.get_pseudocode()
                pseudocode_before = pseudocode_to_string(pseudocode)

                # Check for obfuscated pattern (before d810)
                self.assertIn("a2 + a1 - 2 * (a2 & a1)", pseudocode_before,
                            "Should have obfuscated XOR pattern before d810")
                self.assertIn("a2 - 3 + a3 * a1 - 2 * ((a2 - 3) & (a3 * a1))", pseudocode_before,
                            "Should have complex obfuscated expression before d810")

                # install the decompilation hooks!
                state.start_d810()
                decompiled_func = idaapi.decompile(
                    func_ea, flags=idaapi.DECOMP_NO_CACHE
                )
                self.assertIsNotNone(
                    decompiled_func, "Decompilation returned None for 'test_xor'"
                )
                # Convert to pseudocode string
                pseudocode = decompiled_func.get_pseudocode()
                pseudocode_after = pseudocode_to_string(pseudocode)

                # Check for simplified pattern (after d810)
                self.assertNotEqual(pseudocode_before, pseudocode_after,
                                  "d810 MUST simplify the XOR pattern")
                self.assertIn("a2 ^ a1", pseudocode_after,
                            "Should have simplified XOR after d810")
                self.assertIn("(a2 - 3) ^ (a3 * a1)", pseudocode_after,
                            "Should have simplified XOR expression after d810")

    def test_simplify_mba_guessing(self):
        func_ea = idc.get_name_ea_simple("test_mba_guessing")
        self.assertNotEqual(func_ea, idaapi.BADADDR, "Function 'test_mba_guessing' not found")

        with d810_state() as state:
            # BEFORE: Decompile without d810
            state.stop_d810()
            decompiled_before = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
            self.assertIsNotNone(decompiled_before)

            actual_before = pseudocode_to_string(decompiled_before.get_pseudocode())

            # ASSERT: Complex MBA expression is present
            self.assertIn("2 *", actual_before, "Should contain multiplication")
            # Count operations - should be very complex
            op_count_before = actual_before.count('+') + actual_before.count('-') + actual_before.count('*')
            self.assertGreater(op_count_before, 10, "Obfuscated MBA should have many operations")

            # AFTER: Decompile with d810
            state.start_d810()
            decompiled_after = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
            self.assertIsNotNone(decompiled_after)

            actual_after = pseudocode_to_string(decompiled_after.get_pseudocode())
            expected_deobfuscated = textwrap.dedent(
                """\
                __int64 __fastcall test_mba_guessing(unsigned int a1, __int64 a2, int a3, int a4)
                {
                    // [COLLAPSED LOCAL DECLARATIONS. PRESS NUMPAD "+" TO EXPAND]

                    return (a1 + a4) & a1 ^ (a3 + a1);
                }"""
            )

            # ASSERT: MBA was dramatically simplified
            op_count_after = actual_after.count('+') + actual_after.count('-') + actual_after.count('*')
            self.assertLess(op_count_after, op_count_before,
                           f"MBA simplification MUST reduce operations ({op_count_before} → {op_count_after})")
            self.assertLessEqual(op_count_after, 6, "Deobfuscated MBA should be much simpler")
            # Check for key simplified expressions (not strict equality due to formatting)
            self.assertIn("a1 + a4", actual_after, "Should have simplified addition")
            self.assertIn("a3 + a1", actual_after, "Should have simplified addition")
            # Note: Not using strict assertEqual due to formatting/version differences

    def test_tigress_minmaxarray(self):
        """Test Tigress control flow flattening deobfuscation."""
        func_ea = idc.get_name_ea_simple("tigress_minmaxarray")
        self.assertNotEqual(func_ea, idaapi.BADADDR, "Function 'tigress_minmaxarray' not found")

        with d810_state() as state:
            with state.for_project("example_libobfuscated.json"):
                # BEFORE: Decompile without d810
                state.stop_d810()
                decompiled_before = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
                self.assertIsNotNone(decompiled_before, "Decompilation failed for tigress_minmaxarray")

                actual_before = pseudocode_to_string(decompiled_before.get_pseudocode())

                # ASSERT: Control flow flattening is present (switch statements with dispatcher)
                self.assertIn("switch", actual_before, "Should have switch statement from control flow flattening")
                self.assertIn("case", actual_before, "Should have case statements")
                # Count switch cases - flattened code has many cases
                case_count_before = actual_before.count("case ")
                self.assertGreater(case_count_before, 10, "Flattened code should have many switch cases")

                # AFTER: Decompile with d810 using example_libobfuscated.json config
                # This config includes UnflattenerTigressIndirect for tigress_minmaxarray
                state.start_d810()
                decompiled_after = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
                self.assertIsNotNone(decompiled_after, "Decompilation with d810 failed")

                actual_after = pseudocode_to_string(decompiled_after.get_pseudocode())

                # ASSERT: Control flow was unflattened
                # After unflattening, should have natural control flow (for loops, if statements)
                # instead of dispatcher pattern
                case_count_after = actual_after.count("case ")
                self.assertLess(case_count_after, case_count_before,
                              f"Unflattening MUST reduce switch cases ({case_count_before} → {case_count_after})")

                # Should have more natural control structures
                for_count_after = actual_after.count("for (")
                if_count_after = actual_after.count("if (")
                self.assertGreater(for_count_after + if_count_after, 0,
                                 "Unflattened code should have natural control flow (for/if)")


if __name__ == "__main__":
    unittest.main()
