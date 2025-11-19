import textwrap
import unittest

import idaapi
import idc

from .stutils import d810_state, pseudocode_to_string


class TestLibDeobfuscated(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # Initialize the Hex-Rays decompiler plugin
        if not idaapi.init_hexrays_plugin():
            raise unittest.SkipTest("Hex-Rays decompiler plugin not available")

        idaapi.change_hexrays_config("COLLAPSE_LVARS = YES")

    @classmethod
    def tearDownClass(cls):
        pass

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
            self.assertEqual(actual_after, expected_deobfuscated,
                           "Deobfuscated code should match expected simplified form")

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
            self.assertEqual(actual_after, expected_deobfuscated,
                           "Constant-folded code should match expected form")

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
            self.assertEqual(actual_after, expected_deobfuscated,
                           "Opaque predicates should be resolved to constants")

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
                expected_pseudocode = textwrap.dedent(
                    """\
                __int64 __fastcall test_xor(int a1, int a2, int a3, int *a4)
                {
                    // [COLLAPSED LOCAL DECLARATIONS. PRESS NUMPAD "+" TO EXPAND]

                    *a4 = a2 + a1 - 2 * (a2 & a1);
                    a4[1] = a2 - 3 + a3 * a1 - 2 * ((a2 - 3) & (a3 * a1));
                    return (unsigned int)(a4[1] + *a4);
                }"""
                )
                self.assertEqual(pseudocode_to_string(pseudocode), expected_pseudocode)

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
                expected_pseudocode = textwrap.dedent(
                    """\
                __int64 __fastcall test_xor(int a1, int a2, int a3, int *a4)
                {
                    // [COLLAPSED LOCAL DECLARATIONS. PRESS NUMPAD "+" TO EXPAND]

                    *a4 = a2 ^ a1;
                    a4[1] = (a2 - 3) ^ (a3 * a1);
                    return (unsigned int)(a4[1] + *a4);
                }"""
                )
                self.assertEqual(pseudocode_to_string(pseudocode), expected_pseudocode)

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
            self.assertLess(op_count_after, 6, "Deobfuscated MBA should be much simpler")
            self.assertEqual(actual_after, expected_deobfuscated,
                           "Complex MBA should simplify to expected form")

    def test_tigress_minmaxarray(self):
        obfuscated = textwrap.dedent(
            """\
            __int64 __fastcall tigress_minmaxarray(int a1, char **a2, char **a3)
            {
                // [COLLAPSED LOCAL DECLARATIONS. PRESS NUMPAD "+" TO EXPAND]

                v11 = a3;
                v10 = a2;
                v9 = a1;
                global_argc = a1;
                global_argv = a2;
                global_envp = a3;
                v4 = 0xB;
                while ( 2 )
                {
                    switch ( v4 )
                    {
                        case 0:
                            v8[v7 - 1] = *v10[v7];
                            ++v7;
                            v4 = 0x17;
                            continue;

                        case 1:
                            v6 = v8[v7];
                            v4 = 0x10;
                            continue;

                        case 3:
                            ++v7;
                            v4 = 0xF;
                            continue;

                        case 4:
                            if ( v9 >= 0xB )
                                v4 = 0xD;
                            else
                                v4 = 9;

                            continue;

                        case 7:
                            (*(void (**)(const char *, ...))&_ImageBase.e_magic)("Largest element: %d\n", v6);
                            v5 = v8[0];
                            v7 = 1;
                            v4 = 0xF;
                            continue;

                        case 8:
                            if ( v6 >= v8[v7] )
                                v4 = 0x10;
                            else
                                v4 = 1;

                            continue;

                        case 9:
                            v12 = 1;
                            break;

                        case 0xB:
                            v4 = 4;
                            continue;

                        case 0xC:
                            v6 = v8[0];
                            v7 = 1;
                            v4 = 0x11;
                            continue;

                        case 0xD:
                            v7 = 1;
                            v4 = 0x17;
                            continue;

                        case 0xE:
                            if ( v5 <= v8[v7] )
                                v4 = 3;
                            else
                                v4 = 0x12;

                            continue;

                        case 0xF:
                            if ( v7 >= v9 - 1 )
                                v4 = 0x16;
                            else
                                v4 = 0xE;

                            continue;

                        case 0x10:
                            ++v7;
                            v4 = 0x11;
                            continue;

                        case 0x11:
                            if ( v7 >= v9 - 1 )
                                v4 = 7;
                            else
                                v4 = 8;

                            continue;

                        case 0x12:
                            v5 = v8[v7];
                            v4 = 3;
                            continue;

                        case 0x13:
                            v12 = 0;
                            break;

                        case 0x16:
                            (*(void (**)(const char *, ...))&_ImageBase.e_magic)("Smallest element: %d\n", v5);
                            v4 = 0x13;
                            continue;

                        case 0x17:
                            if ( v7 >= v9 )
                                v4 = 0xC;
                            else
                                v4 = 0;

                            continue;

                        default:
                            continue;
                    }

                    return v12;
                }
            }"""
        )

        deobfuscated = textwrap.dedent(
            """\
            __int64 __fastcall tigress_minmaxarray(int a1, char **a2, char **a3)
            {
                // [COLLAPSED LOCAL DECLARATIONS. PRESS NUMPAD "+" TO EXPAND]

                v12 = a3;
                v11 = a2;
                v10 = a1;
                global_argc = a1;
                global_argv = a2;
                global_envp = a3;
                if ( a1 < 0xB )
                {
                    return 1;
                }
                else
                {
                    for ( i = 1; i < v10; ++i )
                        v9[i - 1] = *v11[i];

                    v5 = v9[0];
                    for ( j = 1; j < v10 - 1; ++j )
                    {
                        if ( v5 < v9[j] )
                            v5 = v9[j];
                    }

                    (*(void (**)(const char *, ...))&_ImageBase.e_magic)("Largest element: %d\n", v5);
                    v4 = v9[0];
                    for ( k = 1; k < v10 - 1; ++k )
                    {
                        if ( v4 > v9[k] )
                            v4 = v9[k];
                    }

                    (*(void (**)(const char *, ...))&_ImageBase.e_magic)("Smallest element: %d\n", v4);
                    return 0;
                }
            }"""
        )


if __name__ == "__main__":
    unittest.main()
