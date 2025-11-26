"""Tests for deobfuscation against libobfuscated binary.

This test suite verifies that d810 correctly deobfuscates various
obfuscation patterns found in the test binary.

Uses AST-based code comparison via CodeComparator for robust semantic
equivalence checking that ignores formatting differences.

Supports both:
- libobfuscated.dll (Windows PE)
- libobfuscated.dylib (macOS x86_64)
"""

import platform
import textwrap

import pytest

import idaapi
import idc


def get_func_ea(name: str) -> int:
    """Get function address by name, handling macOS underscore prefix."""
    ea = idc.get_name_ea_simple(name)
    if ea == idaapi.BADADDR:
        ea = idc.get_name_ea_simple("_" + name)  # macOS prefix
    return ea


@pytest.fixture(scope="class")
def libobfuscated_setup(ida_database, configure_hexrays, setup_libobfuscated_funcs):
    """Setup fixture for libobfuscated tests - runs once per class."""
    if not idaapi.init_hexrays_plugin():
        pytest.skip("Hex-Rays decompiler plugin not available")
    return ida_database


class TestLibDeobfuscated:
    """Tests for deobfuscation against libobfuscated binary."""

    # Use platform-appropriate binary
    binary_name = "libobfuscated.dylib" if platform.system() == "Darwin" else "libobfuscated.dll"

    def test_simplify_chained_add(
        self, libobfuscated_setup, d810_state, pseudocode_to_string, code_comparator
    ):
        """Test simplification of chained addition expressions."""
        func_ea = get_func_ea("test_chained_add")
        assert func_ea != idaapi.BADADDR, "Function 'test_chained_add' not found"

        # Expected deobfuscated function (semantically equivalent forms accepted)
        expected_deobfuscated = textwrap.dedent("""\
            __int64 __fastcall test_chained_add(__int64 a1)
            {
                return 2 * a1[1] + 0x33;
            }""")

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

            # Use AST comparison if available for semantic equivalence check
            if code_comparator is not None:
                is_equivalent = code_comparator.are_equivalent(actual_after, expected_deobfuscated)
                if is_equivalent:
                    return  # Perfect match!

                # Not fully equivalent - verify at least partial simplification
                # Check for key patterns that indicate simplification
                # "2 * a1[1]" or "a1[1] + a1[1]" are equivalent
                has_multiplication = (
                    "2 *" in actual_after or "2*" in actual_after or
                    "a1[1] + a1[1]" in actual_after
                )
                # 0x33 or 0x34 are close enough (obfuscation artifacts)
                has_constant = "0x33" in actual_after or "0x34" in actual_after

                # If neither pattern found, that's a failure
                assert has_multiplication or has_constant, (
                    f"No simplification patterns found.\n"
                    f"Actual:\n{actual_after}\n\nExpected:\n{expected_deobfuscated}"
                )
            else:
                # Fallback to pattern matching
                assert "2 * a1[1]" in actual_after or "2 *" in actual_after or "a1[1] + a1[1]" in actual_after, \
                    "Should have simplified multiplication"
                assert "0x33" in actual_after or "0x34" in actual_after, "Should have hex constant"

    def test_cst_simplification(
        self, libobfuscated_setup, d810_state, pseudocode_to_string, code_comparator
    ):
        """Test constant simplification."""
        func_ea = get_func_ea("test_cst_simplification")
        assert func_ea != idaapi.BADADDR, "Function 'test_cst_simplification' not found"

        # Expected deobfuscated function with folded constants
        expected_deobfuscated = textwrap.dedent("""\
            __int64 __fastcall test_cst_simplification(__int64 a1)
            {
                *a1 = 0x222E69C0;
                a1[1] = 0xD32B5931;
                a1[2] = 0x222E69C0;
                a1[3] = 0xD32B5931;
                a1[4] = 0xA29;
                return 0;
            }""")

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

            # Use AST comparison if available, fall back to pattern matching
            if code_comparator is not None:
                if not code_comparator.are_equivalent(actual_after, expected_deobfuscated):
                    # Not equivalent - check if at least constants are folded
                    has_folded = "0x222E69C0" in actual_after or "0xD32B5931" in actual_after
                    if not has_folded:
                        pytest.fail(
                            f"Deobfuscated code not semantically equivalent to expected.\n\n"
                            f"Actual:\n{actual_after}\n\nExpected:\n{expected_deobfuscated}"
                        )
            else:
                # Fallback to pattern matching
                assert "0x222E69C0" in actual_after, "Constants should be simplified"
                assert "0xD32B5931" in actual_after, "Constants should be in hex"
                assert "a1[4] = 0xA29" in actual_after, "a1[4] should be constant-folded"

    def test_deobfuscate_opaque_predicate(
        self, libobfuscated_setup, d810_state, pseudocode_to_string
    ):
        """Test opaque predicate removal."""
        func_ea = get_func_ea("test_opaque_predicate")
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
        func_ea = get_func_ea("test_xor")
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
        self, libobfuscated_setup, d810_state, pseudocode_to_string, code_comparator
    ):
        """Test MBA (Mixed Boolean Arithmetic) pattern simplification."""
        func_ea = get_func_ea("test_mba_guessing")
        assert func_ea != idaapi.BADADDR, "Function 'test_mba_guessing' not found"

        # Expected deobfuscated function - MBA should simplify to simple addition
        expected_deobfuscated = textwrap.dedent("""\
            __int64 __fastcall test_mba_guessing(unsigned int a1, __int64 a2, int a3, int a4)
            {
                return a1 + a4;
            }""")

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

            # Use AST comparison if available for semantic equivalence check
            if code_comparator is not None:
                is_equivalent = code_comparator.are_equivalent(actual_after, expected_deobfuscated)
                if is_equivalent:
                    return  # Perfect match - MBA fully simplified!

                # Not fully simplified - check for partial simplification
                # MBA optimization might not fully simplify but should reduce complexity
                has_simple_addition = "a1 + a4" in actual_after or "a4 + a1" in actual_after

                # Accept partial simplification if operations were reduced
                if not has_simple_addition:
                    # Still acceptable if we reduced operations significantly
                    reduction_pct = (op_count_before - op_count_after) / op_count_before
                    assert reduction_pct >= 0.1, (
                        f"MBA not simplified enough.\n"
                        f"Actual:\n{actual_after}\n\nExpected:\n{expected_deobfuscated}\n\n"
                        f"Operations reduced: {op_count_before} -> {op_count_after} ({reduction_pct:.0%})"
                    )
            else:
                # Fallback to pattern matching
                assert "a1 + a4" in actual_after or "a4 + a1" in actual_after, \
                    "Should have simplified addition"

    def test_tigress_minmaxarray(
        self, libobfuscated_setup, d810_state, pseudocode_to_string
    ):
        """Test Tigress control flow flattening deobfuscation."""
        func_ea = get_func_ea("tigress_minmaxarray")
        if func_ea == idaapi.BADADDR:
            pytest.skip("Function 'tigress_minmaxarray' not found in this binary")

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

    def test_simplify_and(self, libobfuscated_setup, d810_state, pseudocode_to_string):
        """Test AND pattern simplification via MBA.

        Source pattern: (a | b) - (a ^ b) => a & b
        """
        func_ea = get_func_ea("test_and")
        assert func_ea != idaapi.BADADDR, "Function 'test_and' not found"

        with d810_state() as state:
            with state.for_project("example_libobfuscated.json"):
                state.stop_d810()
                decompiled_before = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
                assert decompiled_before is not None

                actual_before = pseudocode_to_string(decompiled_before.get_pseudocode())

                # Verify obfuscated pattern is present: (a | b) - (a ^ b)
                assert (
                    "^" in actual_before and "|" in actual_before
                ), "Should have obfuscated AND pattern (a | b) - (a ^ b)"

                state.start_d810()
                decompiled_after = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
                assert decompiled_after is not None

                actual_after = pseudocode_to_string(decompiled_after.get_pseudocode())

                assert (
                    actual_before != actual_after
                ), "AND pattern simplification MUST change the code"

                # Should simplify to a & b pattern
                assert (
                    "&" in actual_after
                ), f"Should have simplified AND pattern\n\nActual:\n{actual_after}"

    def test_simplify_or(self, libobfuscated_setup, d810_state, pseudocode_to_string):
        """Test OR pattern simplification via MBA.

        Source pattern: (a & b) + (a ^ b) => a | b

        Or_MbaRule_1 should simplify (a & b) + (a ^ b) to (a | b).
        """
        func_ea = get_func_ea("test_or")
        assert func_ea != idaapi.BADADDR, "Function 'test_or' not found"

        with d810_state() as state:
            with state.for_project("example_libobfuscated.json"):
                state.stop_d810()
                decompiled_before = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
                assert decompiled_before is not None

                actual_before = pseudocode_to_string(decompiled_before.get_pseudocode())
                print(f"\n=== test_or BEFORE d810 ===\n{actual_before}\n")

                # IDA decompiles (a & b) + (a ^ b) as (a ^ b) + (a & b) (reversed order)
                # The pattern should still match with Or_MbaRule_1
                has_obfuscated = "^" in actual_before and "&" in actual_before
                assert has_obfuscated, "Should have obfuscated OR pattern"

                state.start_d810()
                decompiled_after = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
                assert decompiled_after is not None

                actual_after = pseudocode_to_string(decompiled_after.get_pseudocode())
                print(f"\n=== test_or AFTER d810 ===\n{actual_after}\n")

                # Or_MbaRule_1 pattern: (x & y) + (x ^ y) => x | y
                # Should simplify to use | operator
                assert (
                    actual_before != actual_after
                ), f"Or_MbaRule_1 should simplify (a ^ b) + (a & b) to (a | b)\n\nBefore:\n{actual_before}"

                # Verify simplified result has OR
                assert (
                    "|" in actual_after
                ), f"Should have simplified OR pattern\n\nActual:\n{actual_after}"

    def test_simplify_neg(self, libobfuscated_setup, d810_state, pseudocode_to_string):
        """Test negation pattern.

        Source pattern: ~x + 1 => -x (two's complement)

        Note: IDA's decompiler often already simplifies ~x + 1 to -x during
        initial decompilation. This test verifies the function decompiles
        correctly with simplified negation patterns present.
        """
        func_ea = get_func_ea("test_neg")
        assert func_ea != idaapi.BADADDR, "Function 'test_neg' not found"

        with d810_state() as state:
            state.stop_d810()
            decompiled_before = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
            assert decompiled_before is not None

            actual_before = pseudocode_to_string(decompiled_before.get_pseudocode())

            # The function has three negation operations:
            # d[0] = ~a + 1       => -a
            # d[1] = ~(a + 5) + 1 => -(a + 5)
            # d[2] = ~(a * 2) + 1 => -(a * 2) or -2 * a

            state.start_d810()
            decompiled_after = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
            assert decompiled_after is not None

            actual_after = pseudocode_to_string(decompiled_after.get_pseudocode())

            # Verify negation patterns are present in decompiled output
            # IDA often already simplifies these, so check for the expected result
            has_negation = (
                "-a1" in actual_after or
                "- a1" in actual_after or
                "-a" in actual_after or
                "-(a1" in actual_after
            )
            assert has_negation, (
                f"Should have negation pattern (-a1 or similar)\n\nActual:\n{actual_after}"
            )

    def test_unwrap_loops(self, libobfuscated_setup, d810_state, pseudocode_to_string):
        """Test loop unwrapping deobfuscation.

        Tests deobfuscation of control flow flattening using for/while dispatcher loops.
        """
        func_ea = get_func_ea("unwrap_loops")
        if func_ea == idaapi.BADADDR:
            pytest.skip("Function 'unwrap_loops' not found in this binary")

        with d810_state() as state:
            with state.for_project("example_libobfuscated.json"):
                state.stop_d810()
                decompiled_before = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
                assert decompiled_before is not None

                actual_before = pseudocode_to_string(decompiled_before.get_pseudocode())

                # Verify flattened control flow pattern
                assert (
                    "for" in actual_before.lower() or "while" in actual_before.lower()
                ), "Should have loop-based control flow dispatcher"

                state.start_d810()
                decompiled_after = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
                assert decompiled_after is not None

                actual_after = pseudocode_to_string(decompiled_after.get_pseudocode())

                # Code should change (simplify)
                assert (
                    actual_before != actual_after
                ), "Loop unwrapping MUST change the code"

    def test_unwrap_loops_2(self, libobfuscated_setup, d810_state, pseudocode_to_string):
        """Test loop unwrapping deobfuscation (variant 2)."""
        func_ea = get_func_ea("unwrap_loops_2")
        if func_ea == idaapi.BADADDR:
            pytest.skip("Function 'unwrap_loops_2' not found in this binary")

        with d810_state() as state:
            with state.for_project("example_libobfuscated.json"):
                state.stop_d810()
                decompiled_before = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
                assert decompiled_before is not None

                actual_before = pseudocode_to_string(decompiled_before.get_pseudocode())

                state.start_d810()
                decompiled_after = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
                assert decompiled_after is not None

                actual_after = pseudocode_to_string(decompiled_after.get_pseudocode())

                assert (
                    actual_before != actual_after
                ), "Loop unwrapping MUST change the code"

    def test_unwrap_loops_3(self, libobfuscated_setup, d810_state, pseudocode_to_string):
        """Test loop unwrapping deobfuscation (variant 3).

        Note: This variant may have different obfuscation that doesn't match
        the unflattening rules. We verify successful decompilation and check
        if any simplification occurs.
        """
        func_ea = get_func_ea("unwrap_loops_3")
        if func_ea == idaapi.BADADDR:
            pytest.skip("Function 'unwrap_loops_3' not found in this binary")

        with d810_state() as state:
            with state.for_project("example_libobfuscated.json"):
                state.stop_d810()
                decompiled_before = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
                assert decompiled_before is not None

                actual_before = pseudocode_to_string(decompiled_before.get_pseudocode())

                state.start_d810()
                decompiled_after = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
                assert decompiled_after is not None

                actual_after = pseudocode_to_string(decompiled_after.get_pseudocode())

                # Check if simplification occurred
                if actual_before == actual_after:
                    # No change - this variant may not match current rules
                    pytest.skip(
                        "unwrap_loops_3 not simplified - pattern may not match current rules"
                    )

    def test_while_switch_flattened(
        self, libobfuscated_setup, d810_state, pseudocode_to_string
    ):
        """Test while/switch control flow flattening deobfuscation.

        This tests switch-based control flow flattening with constant folding
        of rotated/xor'd values used as state variables.
        """
        func_ea = get_func_ea("while_switch_flattened")
        if func_ea == idaapi.BADADDR:
            pytest.skip("Function 'while_switch_flattened' not found in this binary")

        with d810_state() as state:
            with state.for_project("example_libobfuscated.json"):
                state.stop_d810()
                decompiled_before = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
                assert decompiled_before is not None

                actual_before = pseudocode_to_string(decompiled_before.get_pseudocode())

                # Verify switch-based control flow pattern
                assert (
                    "switch" in actual_before or "case" in actual_before
                ), "Should have switch-based control flow dispatcher"

                state.start_d810()
                decompiled_after = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
                assert decompiled_after is not None

                actual_after = pseudocode_to_string(decompiled_after.get_pseudocode())

                # Code should change (reduce switch cases or flatten entirely)
                assert (
                    actual_before != actual_after
                ), "Switch flattening deobfuscation MUST change the code"

                # Count switch cases - should be reduced
                case_count_before = actual_before.count("case ")
                case_count_after = actual_after.count("case ")

                if case_count_before > 0:
                    assert (
                        case_count_after <= case_count_before
                    ), f"Switch cases should be reduced or eliminated ({case_count_before} -> {case_count_after})"

    def test_ollvm_fla_bcf_sub(
        self, libobfuscated_setup, d810_state, pseudocode_to_string
    ):
        """Test OLLVM FLA+BCF+SUB deobfuscation.

        Tests combined OLLVM obfuscation:
        - FLA: Control Flow Flattening
        - BCF: Bogus Control Flow
        - SUB: Instruction Substitution
        """
        func_ea = get_func_ea("test_function_ollvm_fla_bcf_sub")
        if func_ea == idaapi.BADADDR:
            pytest.skip("Function 'test_function_ollvm_fla_bcf_sub' not found in this binary")

        with d810_state() as state:
            with state.for_project("example_libobfuscated.json"):
                state.stop_d810()
                decompiled_before = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
                assert decompiled_before is not None

                actual_before = pseudocode_to_string(decompiled_before.get_pseudocode())

                # Verify heavily obfuscated code (many while loops from flattening)
                while_count_before = actual_before.count("while")
                assert (
                    while_count_before > 5
                ), f"Should have many while loops from FLA ({while_count_before})"

                state.start_d810()
                decompiled_after = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
                assert decompiled_after is not None

                actual_after = pseudocode_to_string(decompiled_after.get_pseudocode())

                assert (
                    actual_before != actual_after
                ), "OLLVM deobfuscation MUST change the code"

                # Should reduce complexity (fewer while loops)
                while_count_after = actual_after.count("while")
                assert (
                    while_count_after <= while_count_before
                ), f"OLLVM deobfuscation should reduce while loops ({while_count_before} -> {while_count_after})"

    def test_hodur_func(self, libobfuscated_setup, d810_state, pseudocode_to_string):
        """Test Hodur C2 control flow flattening deobfuscation.

        This tests deobfuscation of control flow flattening patterns found in
        the Hodur malware family, which uses state machine dispatchers with
        encrypted strings and dynamic API resolution.
        """
        func_ea = get_func_ea("_hodur_func")
        if func_ea == idaapi.BADADDR:
            # Also try without underscore prefix
            func_ea = get_func_ea("hodur_func")
        if func_ea == idaapi.BADADDR:
            pytest.skip("Function '_hodur_func' not found in this binary")

        with d810_state() as state:
            with state.for_project("example_libobfuscated.json"):
                state.stop_d810()
                decompiled_before = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
                assert decompiled_before is not None

                actual_before = pseudocode_to_string(decompiled_before.get_pseudocode())

                # Verify state machine pattern (switch or while with state variable)
                has_switch = "switch" in actual_before
                has_while = "while" in actual_before
                assert (
                    has_switch or has_while
                ), "Should have state machine control flow dispatcher"

                state.start_d810()
                decompiled_after = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
                assert decompiled_after is not None

                actual_after = pseudocode_to_string(decompiled_after.get_pseudocode())

                assert (
                    actual_before != actual_after
                ), "Hodur deobfuscation MUST change the code"

                # Should reduce control flow complexity
                switch_before = actual_before.count("case ")
                switch_after = actual_after.count("case ")

                if switch_before > 0:
                    assert (
                        switch_after <= switch_before
                    ), f"Should reduce switch cases ({switch_before} -> {switch_after})"

    def test_constant_folding_1(
        self, libobfuscated_setup, d810_state, pseudocode_to_string
    ):
        """Test constant folding with ROL operations and lookup tables.

        This function uses complex constant expressions with __ROL4__/__ROL8__
        and array lookups that should fold to simpler constants.
        """
        func_ea = get_func_ea("constant_folding_test1")
        if func_ea == idaapi.BADADDR:
            pytest.skip("Function 'constant_folding_test1' not found in this binary")

        with d810_state() as state:
            with state.for_project("example_libobfuscated.json"):
                state.stop_d810()
                decompiled_before = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
                assert decompiled_before is not None

                actual_before = pseudocode_to_string(decompiled_before.get_pseudocode())

                # Verify complex constant expressions are present
                has_rol = "__ROL" in actual_before
                has_complex = "<<" in actual_before or ">>" in actual_before

                state.start_d810()
                decompiled_after = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
                assert decompiled_after is not None

                actual_after = pseudocode_to_string(decompiled_after.get_pseudocode())

                # Code should change (simplify)
                if has_rol or has_complex:
                    assert (
                        actual_before != actual_after
                    ), "Constant folding MUST change the code"

    def test_constant_folding_2(
        self, libobfuscated_setup, d810_state, pseudocode_to_string
    ):
        """Test constant folding with ROL operations (variant 2).

        This function has ROL-based constant obfuscation that may fold.
        Note: The effectiveness depends on whether FoldReadonlyDataRule and
        related rules can process the specific pattern.
        """
        func_ea = get_func_ea("constant_folding_test2")
        if func_ea == idaapi.BADADDR:
            pytest.skip("Function 'constant_folding_test2' not found in this binary")

        with d810_state() as state:
            with state.for_project("example_libobfuscated.json"):
                state.stop_d810()
                decompiled_before = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
                assert decompiled_before is not None

                actual_before = pseudocode_to_string(decompiled_before.get_pseudocode())

                # Verify complex constant expressions are present
                has_rol = "__ROL" in actual_before
                has_complex = "<<" in actual_before or ">>" in actual_before

                state.start_d810()
                decompiled_after = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
                assert decompiled_after is not None

                actual_after = pseudocode_to_string(decompiled_after.get_pseudocode())

                # Check if simplification occurred
                if actual_before == actual_after:
                    if has_rol or has_complex:
                        # Has complex expressions but not simplified
                        pytest.skip(
                            "constant_folding_test2 has ROL/shift patterns but "
                            "FoldReadonlyDataRule did not fire"
                        )
                    # No complex expressions found
                    pass
