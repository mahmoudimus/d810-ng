"""Tests for deobfuscation against libobfuscated.dll.

This test suite verifies that d810 correctly deobfuscates various
obfuscation patterns found in the test binary.
"""

import pytest

import idaapi
import idc


@pytest.fixture(scope="class")
def libobfuscated_setup(ida_database, configure_hexrays, setup_libobfuscated_funcs):
    """Setup fixture for libobfuscated tests - runs once per class."""
    if not idaapi.init_hexrays_plugin():
        pytest.skip("Hex-Rays decompiler plugin not available")
    return ida_database


class TestLibDeobfuscated:
    """Tests for deobfuscation against libobfuscated.dll."""

    binary_name = "libobfuscated.dll"

    def test_simplify_chained_add(
        self, libobfuscated_setup, d810_state, pseudocode_to_string
    ):
        """Test simplification of chained addition expressions."""
        func_ea = idc.get_name_ea_simple("test_chained_add")
        assert func_ea != idaapi.BADADDR, "Function 'test_chained_add' not found"

        with d810_state() as state:
            # BEFORE: Decompile without d810 (obfuscated)
            state.stop_d810()
            decompiled_before = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
            assert (
                decompiled_before is not None
            ), "Decompilation failed for test_chained_add"

            actual_before = pseudocode_to_string(decompiled_before.get_pseudocode())

            # ASSERT: Obfuscated pattern is present
            assert (
                "0xFFFFFFEF" in actual_before
            ), "Unoptimized code should contain complex expressions"

            # AFTER: Decompile with d810 (deobfuscated)
            state.start_d810()
            decompiled_after = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
            assert decompiled_after is not None, "Decompilation with d810 failed"

            actual_after = pseudocode_to_string(decompiled_after.get_pseudocode())

            # ASSERT: Deobfuscation happened
            assert actual_before != actual_after, "Deobfuscation MUST change the code"
            assert "2 * a1[1]" in actual_after, "Should have simplified multiplication"
            assert "0x33" in actual_after, "Should have hex constant"

    def test_cst_simplification(
        self, libobfuscated_setup, d810_state, pseudocode_to_string
    ):
        """Test constant simplification."""
        func_ea = idc.get_name_ea_simple("test_cst_simplification")
        assert func_ea != idaapi.BADADDR, "Function 'test_cst_simplification' not found"

        with d810_state() as state:
            state.stop_d810()
            decompiled_before = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
            assert decompiled_before is not None

            actual_before = pseudocode_to_string(decompiled_before.get_pseudocode())

            assert (
                "0x222E69C2" in actual_before
            ), "Should contain complex constant expressions"
            assert (
                "0x50211120" in actual_before
            ), "Should contain complex constant operations"

            state.start_d810()
            decompiled_after = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
            assert decompiled_after is not None

            actual_after = pseudocode_to_string(decompiled_after.get_pseudocode())

            assert (
                actual_before != actual_after
            ), "Constant folding MUST change the code"
            assert "0x222E69C0" in actual_after, "Constants should be simplified"
            assert "0xD32B5931" in actual_after, "Constants should be in hex"
            assert "a1[4] = 0xA29" in actual_after, "a1[4] should be constant-folded"

    def test_deobfuscate_opaque_predicate(
        self, libobfuscated_setup, d810_state, pseudocode_to_string
    ):
        """Test opaque predicate removal."""
        func_ea = idc.get_name_ea_simple("test_opaque_predicate")
        assert func_ea != idaapi.BADADDR, "Function 'test_opaque_predicate' not found"

        with d810_state() as state:
            state.stop_d810()
            decompiled_before = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
            assert decompiled_before is not None

            actual_before = pseudocode_to_string(decompiled_before.get_pseudocode())

            assert (
                "v4" in actual_before
            ), "Should have variable v4 from opaque predicate"
            assert (
                "v3" in actual_before
            ), "Should have variable v3 from opaque predicate"

            state.start_d810()
            decompiled_after = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
            assert decompiled_after is not None

            actual_after = pseudocode_to_string(decompiled_after.get_pseudocode())

            assert (
                actual_before != actual_after
            ), "Opaque predicate removal MUST change code"
            assert "= 1;" in actual_after, "Should have constant 1"

    def test_simplify_xor(self, libobfuscated_setup, d810_state, pseudocode_to_string):
        """Test XOR pattern simplification."""
        func_ea = idc.get_name_ea_simple("test_xor")
        assert func_ea != idaapi.BADADDR, "Function 'test_xor' not found in database"

        with d810_state() as state:
            with state.for_project("example_libobfuscated.json"):
                state.stop_d810()

                decompiled_func = idaapi.decompile(
                    func_ea, flags=idaapi.DECOMP_NO_CACHE
                )
                assert (
                    decompiled_func is not None
                ), "Decompilation returned None for 'test_xor'"

                pseudocode_before = pseudocode_to_string(
                    decompiled_func.get_pseudocode()
                )

                assert (
                    "a2 + a1 - 2 * (a2 & a1)" in pseudocode_before
                ), "Should have obfuscated XOR pattern before d810"
                assert (
                    "a2 - 3 + a3 * a1 - 2 * ((a2 - 3) & (a3 * a1))" in pseudocode_before
                ), "Should have complex obfuscated expression before d810"

                state.start_d810()
                decompiled_func = idaapi.decompile(
                    func_ea, flags=idaapi.DECOMP_NO_CACHE
                )
                assert (
                    decompiled_func is not None
                ), "Decompilation returned None for 'test_xor'"

                pseudocode_after = pseudocode_to_string(
                    decompiled_func.get_pseudocode()
                )

                assert (
                    pseudocode_before != pseudocode_after
                ), "d810 MUST simplify the XOR pattern"
                assert (
                    "a2 ^ a1" in pseudocode_after
                ), "Should have simplified XOR after d810"
                assert (
                    "(a2 - 3) ^ (a3 * a1)" in pseudocode_after
                ), "Should have simplified XOR expression after d810"

    def test_simplify_mba_guessing(
        self, libobfuscated_setup, d810_state, pseudocode_to_string
    ):
        """Test MBA (Mixed Boolean Arithmetic) pattern simplification."""
        func_ea = idc.get_name_ea_simple("test_mba_guessing")
        assert func_ea != idaapi.BADADDR, "Function 'test_mba_guessing' not found"

        with d810_state() as state:
            state.stop_d810()
            decompiled_before = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
            assert decompiled_before is not None

            actual_before = pseudocode_to_string(decompiled_before.get_pseudocode())

            assert "2 *" in actual_before, "Should contain multiplication"
            op_count_before = (
                actual_before.count("+")
                + actual_before.count("-")
                + actual_before.count("*")
            )
            assert op_count_before > 10, "Obfuscated MBA should have many operations"

            state.start_d810()
            decompiled_after = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
            assert decompiled_after is not None

            actual_after = pseudocode_to_string(decompiled_after.get_pseudocode())

            op_count_after = (
                actual_after.count("+")
                + actual_after.count("-")
                + actual_after.count("*")
            )
            assert (
                op_count_after < op_count_before
            ), f"MBA simplification MUST reduce operations ({op_count_before} -> {op_count_after})"
            assert "a1 + a4" in actual_after, "Should have simplified addition"

    @pytest.mark.skip(
        reason="Tigress unflattening requires address-specific config (32-bit vs 64-bit mismatch)"
    )
    def test_tigress_minmaxarray(
        self, libobfuscated_setup, d810_state, pseudocode_to_string
    ):
        """Test Tigress control flow flattening deobfuscation."""
        func_ea = idc.get_name_ea_simple("tigress_minmaxarray")
        assert func_ea != idaapi.BADADDR, "Function 'tigress_minmaxarray' not found"

        with d810_state() as state:
            with state.for_project("example_libobfuscated.json"):
                state.stop_d810()
                decompiled_before = idaapi.decompile(
                    func_ea, flags=idaapi.DECOMP_NO_CACHE
                )
                assert (
                    decompiled_before is not None
                ), "Decompilation failed for tigress_minmaxarray"

                actual_before = pseudocode_to_string(decompiled_before.get_pseudocode())

                assert "switch" in actual_before, "Should have switch statement"
                assert "case" in actual_before, "Should have case statements"
                case_count_before = actual_before.count("case ")
                assert (
                    case_count_before > 10
                ), "Flattened code should have many switch cases"

                state.start_d810()
                decompiled_after = idaapi.decompile(
                    func_ea, flags=idaapi.DECOMP_NO_CACHE
                )
                assert decompiled_after is not None, "Decompilation with d810 failed"

                actual_after = pseudocode_to_string(decompiled_after.get_pseudocode())

                case_count_after = actual_after.count("case ")
                assert (
                    case_count_after < case_count_before
                ), f"Unflattening MUST reduce switch cases ({case_count_before} -> {case_count_after})"

                for_count_after = actual_after.count("for (")
                if_count_after = actual_after.count("if (")
                assert (
                    for_count_after + if_count_after > 0
                ), "Unflattened code should have natural control flow (for/if)"
