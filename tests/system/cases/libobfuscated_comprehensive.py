"""Comprehensive test cases for libobfuscated binary.

This module defines ALL deobfuscation test cases from samples/src/c/ as data
using the DeobfuscationCase DSL. Organized by source file for easy reference.

To run: pytest tests/system/test_libdeobfuscated_dsl.py -v
"""

from d810.testing import DeobfuscationCase, BinaryOverride


# =============================================================================
# manually_obfuscated.c - MBA and basic patterns
# =============================================================================

MANUALLY_OBFUSCATED_CASES = [
    DeobfuscationCase(
        function="test_chained_add",
        description="Chained addition expressions with nested operations",
        project="default_instruction_only.json",
        obfuscated_contains=["0xFFFFFFEF"],
        expected_code="""
            __int64 __fastcall test_chained_add(__int64 a1)
            {
                return 2 * a1[1] + 0x33;
            }
        """,
        acceptable_patterns=["2 * a1[1]", "a1[1] + a1[1]", "0x33", "0x34"],
    ),
    DeobfuscationCase(
        function="test_cst_simplification",
        description="Constant simplification with bitwise AND/OR/XOR",
        project="default_instruction_only.json",
        obfuscated_contains=["0x222E69C2", "0x50211120"],
        acceptable_patterns=["0x222E69C0", "0xD32B5931", "0xA29"],
    ),
    DeobfuscationCase(
        function="test_opaque_predicate",
        description="Opaque predicate patterns that always evaluate to known values",
        project="example_libobfuscated.json",
        obfuscated_contains=["v4", "v3"],
        deobfuscated_contains=["= 1;"],
    ),
    DeobfuscationCase(
        function="test_xor",
        description="XOR MBA pattern: (a + b) - 2*(a & b) => a ^ b",
        project="example_libobfuscated.json",
        obfuscated_contains=["a2 + a1 - 2 * (a2 & a1)"],
        deobfuscated_contains=["a2 ^ a1", "(a2 - 3) ^ (a3 * a1)"],
    ),
    DeobfuscationCase(
        function="test_or",
        description="OR MBA pattern: (a & b) + (a ^ b) => a | b",
        project="example_libobfuscated.json",
        obfuscated_contains=["^", "&"],
        deobfuscated_contains=["|"],
    ),
    DeobfuscationCase(
        function="test_and",
        description="AND MBA pattern: (a | b) - (a ^ b) => a & b",
        project="example_libobfuscated.json",
        obfuscated_contains=["^", "|"],
        deobfuscated_contains=["&"],
    ),
    DeobfuscationCase(
        function="test_neg",
        description="Negation pattern: ~x + 1 => -x (two's complement)",
        project="default_instruction_only.json",
        # IDA often already simplifies, just verify negation present
        acceptable_patterns=["-a1", "- a1", "-a", "-(a1"],
    ),
    DeobfuscationCase(
        function="test_mba_guessing",
        description="Complex MBA with nested bitwise operations",
        project="default_instruction_only.json",
        obfuscated_contains=["2 *"],
        expected_code="""
            __int64 __fastcall test_mba_guessing(unsigned int a1, __int64 a2, int a3, int a4)
            {
                return a1 + a4;
            }
        """,
        acceptable_patterns=["a1 + a4", "a4 + a1"],
    ),
]


# =============================================================================
# abc_f6_constants.c - ABC pattern with F6xxx magic constants
# =============================================================================

ABC_F6_CASES = [
    DeobfuscationCase(
        function="abc_f6_add_dispatch",
        description="ABC pattern with ADD using F6xxx magic constants",
        project="default_unflattening_approov.json",
        obfuscated_contains=["0xF6"],
        must_change=True,
    ),
    DeobfuscationCase(
        function="abc_f6_sub_dispatch",
        description="ABC pattern using SUB with F6xxx constants",
        project="default_unflattening_approov.json",
        obfuscated_contains=["0xF6"],
        must_change=True,
    ),
    DeobfuscationCase(
        function="abc_f6_xor_dispatch",
        description="ABC pattern with XOR-based state transitions",
        project="default_unflattening_approov.json",
        obfuscated_contains=["0xF6"],
        must_change=True,
    ),
    DeobfuscationCase(
        function="abc_f6_or_dispatch",
        description="ABC pattern with OR operations on state variables",
        project="default_unflattening_approov.json",
        obfuscated_contains=["0xF6"],
        must_change=True,
    ),
    DeobfuscationCase(
        function="abc_f6_nested",
        description="Nested conditional ABC pattern",
        project="default_unflattening_approov.json",
        obfuscated_contains=["0xF6"],
        must_change=True,
    ),
    DeobfuscationCase(
        function="abc_f6_64bit_pattern",
        description="ABC pattern with 64-bit magic constants",
        project="default_unflattening_approov.json",
        must_change=True,
    ),
]


# =============================================================================
# abc_xor_dispatch.c - XOR/OR based dispatchers
# =============================================================================

ABC_XOR_CASES = [
    DeobfuscationCase(
        function="abc_xor_dispatch",
        description="XOR-based flattened control flow dispatcher",
        project="default_unflattening_approov.json",
        must_change=True,
    ),
    DeobfuscationCase(
        function="abc_or_dispatch",
        description="OR-based state manipulation with mask operations",
        project="default_unflattening_approov.json",
        must_change=True,
    ),
    DeobfuscationCase(
        function="abc_mixed_dispatch",
        description="Combined XOR/OR state transitions",
        project="default_unflattening_approov.json",
        must_change=True,
    ),
]


# =============================================================================
# approov_flattened.c - Approov-style obfuscation
# =============================================================================

APPROOV_CASES = [
    DeobfuscationCase(
        function="approov_real_pattern",
        description="Exact decompiled output from real Approov-obfuscated code",
        project="default_unflattening_approov.json",
        must_change=True,
    ),
    DeobfuscationCase(
        function="approov_simplified",
        description="Simplified Approov pattern using while(!=)",
        project="default_unflattening_approov.json",
        must_change=True,
    ),
    DeobfuscationCase(
        function="approov_multistate",
        description="Approov pattern with multiple state transitions",
        project="default_unflattening_approov.json",
        must_change=True,
    ),
    DeobfuscationCase(
        function="approov_vm_dispatcher",
        description="Approov VM dispatcher using switch statement",
        project="default_unflattening_approov.json",
        obfuscated_contains=["switch"],
        must_change=True,
    ),
    DeobfuscationCase(
        function="approov_goto_dispatcher",
        description="Approov pattern using explicit goto statements",
        project="default_unflattening_approov.json",
        must_change=True,
    ),
    DeobfuscationCase(
        function="approov_simple_loop",
        description="Simple loop pattern generating jz instruction",
        project="default_unflattening_approov.json",
        must_change=True,
    ),
]


# =============================================================================
# constant_folding.c - Constant folding patterns
# =============================================================================

CONSTANT_FOLDING_CASES = [
    DeobfuscationCase(
        function="constant_folding_test1",
        description="Constant folding with ROL operations and lookup tables",
        project="example_libobfuscated.json",
        # Verify FoldReadonlyDataRule fires
        required_rules=["FoldReadonlyDataRule"],
        must_change=True,
    ),
    DeobfuscationCase(
        function="constant_folding_test2",
        description="Constant folding with bitwise operations",
        project="example_libobfuscated.json",
        must_change=True,
    ),
    DeobfuscationCase(
        function="sub_180001000",
        description="Complex constant folding with nested rotations",
        project="example_libobfuscated.json",
        # May not change if pattern doesn't match
        must_change=False,
    ),
    DeobfuscationCase(
        function="outlined_helper_1",
        description="Helper function for constant folding with memory ops",
        project="example_libobfuscated.json",
        must_change=False,
    ),
    DeobfuscationCase(
        function="outlined_helper_2",
        description="Helper function for constant folding with pointers",
        project="example_libobfuscated.json",
        must_change=False,
    ),
    DeobfuscationCase(
        function="AntiDebug_ExceptionFilter",
        description="Anti-debugging exception handler with constant folding",
        project="example_libobfuscated.json",
        must_change=False,
    ),
]


# =============================================================================
# dispatcher_patterns.c - Various dispatcher detection patterns
# =============================================================================

DISPATCHER_PATTERN_CASES = [
    DeobfuscationCase(
        function="high_fan_in_pattern",
        description="HIGH_FAN_IN dispatcher with multiple case blocks",
        project="default_unflattening_ollvm.json",
        must_change=True,
    ),
    DeobfuscationCase(
        function="state_comparison_pattern",
        description="STATE_COMPARISON pattern with large constants",
        project="default_unflattening_ollvm.json",
        obfuscated_contains=["0x10000"],
        must_change=True,
    ),
    DeobfuscationCase(
        function="nested_while_hodur_pattern",
        description="NESTED_LOOP pattern with Hodur-style while(1) loops",
        project="example_hodur.json",
        obfuscated_contains=["while"],
        must_change=True,
    ),
    DeobfuscationCase(
        function="switch_case_ollvm_pattern",
        description="SWITCH_JUMP pattern with O-LLVM style jtbl",
        project="default_unflattening_ollvm.json",
        obfuscated_contains=["switch", "case"],
        must_change=True,
    ),
    DeobfuscationCase(
        function="mixed_dispatcher_pattern",
        description="Combination of multiple dispatcher strategies",
        project="default_unflattening_ollvm.json",
        must_change=True,
    ),
    DeobfuscationCase(
        function="predecessor_uniformity_pattern",
        description="PREDECESSOR_UNIFORM detection pattern",
        project="default_unflattening_ollvm.json",
        must_change=True,
    ),
    DeobfuscationCase(
        function="test_all_patterns",
        description="Test harness calling all dispatcher patterns",
        project="default_unflattening_ollvm.json",
        must_change=False,  # This is just a caller
    ),
]


# =============================================================================
# exception_paths.c - Exception/edge cases
# =============================================================================

EXCEPTION_PATH_CASES = [
    DeobfuscationCase(
        function="unresolvable_external",
        description="NotResolvableFatherException - state from external function",
        project="default_unflattening_ollvm.json",
        # These test exception paths - may not change
        must_change=False,
    ),
    DeobfuscationCase(
        function="unresolvable_computed",
        description="State computation from input prevents resolution",
        project="default_unflattening_ollvm.json",
        must_change=False,
    ),
    DeobfuscationCase(
        function="non_duplicable_side_effects",
        description="NotDuplicableFatherException - side effects block duplication",
        project="default_unflattening_ollvm.json",
        must_change=False,
    ),
    DeobfuscationCase(
        function="deep_duplication_path",
        description="Tests MAX_DUPLICATION_PASSES limit with 25+ states",
        project="default_unflattening_ollvm.json",
        must_change=False,
    ),
    DeobfuscationCase(
        function="loop_dependent_state",
        description="State dependent on loop iteration (partial resolution)",
        project="default_unflattening_ollvm.json",
        must_change=False,
    ),
    DeobfuscationCase(
        function="indirect_state_pointer",
        description="Indirect dispatcher with state loaded through pointer",
        project="default_unflattening_ollvm.json",
        must_change=False,
    ),
    DeobfuscationCase(
        function="external_transform_state",
        description="State modified by external function",
        project="default_unflattening_ollvm.json",
        must_change=False,
    ),
]


# =============================================================================
# hodur_c2_flattened.c - Hodur malware patterns
# =============================================================================

HODUR_CASES = [
    DeobfuscationCase(
        function="_hodur_func",
        description="Main Hodur C2 flattened function",
        project="example_hodur.json",
        obfuscated_contains=["switch", "while"],
        # Must preserve API calls
        acceptable_patterns=["printf", "resolve_api", "WinHttp"],
    ),
    DeobfuscationCase(
        function="resolve_api",
        description="Dynamic API resolution helper",
        project="example_hodur.json",
        must_change=False,  # Helper function, not obfuscated
    ),
]


# =============================================================================
# nested_dispatchers.c - Nested dispatcher patterns
# =============================================================================

NESTED_DISPATCHER_CASES = [
    DeobfuscationCase(
        function="nested_simple",
        description="Simple nested dispatcher with outer/inner state machines",
        project="default_unflattening_ollvm.json",
        must_change=True,
    ),
    DeobfuscationCase(
        function="nested_deep",
        description="Deeply nested dispatchers (3 levels: L1 -> L2 -> L3)",
        project="default_unflattening_ollvm.json",
        must_change=True,
    ),
    DeobfuscationCase(
        function="nested_parallel",
        description="Parallel nested dispatchers at same nesting level",
        project="default_unflattening_ollvm.json",
        must_change=True,
    ),
    DeobfuscationCase(
        function="nested_shared_blocks",
        description="Dispatcher with shared internal blocks",
        project="default_unflattening_ollvm.json",
        must_change=True,
    ),
]


# =============================================================================
# ollvm_obfuscated.c - O-LLVM patterns
# =============================================================================

OLLVM_CASES = [
    DeobfuscationCase(
        function="test_function_ollvm_fla_bcf_sub",
        description="O-LLVM FLA+BCF+SUB combined obfuscation",
        project="example_libobfuscated.json",
        obfuscated_contains=["while"],
        must_change=True,
    ),
]


# =============================================================================
# tigress_obfuscated.c - Tigress patterns
# =============================================================================

TIGRESS_CASES = [
    DeobfuscationCase(
        function="tigress_minmaxarray",
        description="Tigress flattened min/max array search",
        project="example_libobfuscated.json",
        obfuscated_contains=["switch", "case"],
        must_change=True,
    ),
]


# =============================================================================
# unwrap_loops.c - Loop unwrapping patterns
# =============================================================================

UNWRAP_LOOPS_CASES = [
    DeobfuscationCase(
        function="unwrap_loops",
        description="Loop unwrapping with spin-lock synchronization",
        project="example_libobfuscated.json",
        must_change=True,
    ),
    DeobfuscationCase(
        function="unwrap_loops_2",
        description="Loop unwrapping with dynamic size calculations",
        project="example_libobfuscated.json",
        must_change=True,
    ),
    DeobfuscationCase(
        function="unwrap_loops_3",
        description="Complex loop pattern with hidden C++ exception states",
        project="example_libobfuscated.json",
        must_change=False,  # May not match current rules
    ),
    DeobfuscationCase(
        function="SafeCloseHandle",
        description="Loop unwrapping with handle validation",
        project="example_libobfuscated.json",
        must_change=False,
    ),
    DeobfuscationCase(
        function="bogus_loops",
        description="Bogus/redundant loop patterns",
        project="bogus_loops.json",
        must_change=True,
    ),
]


# =============================================================================
# while_switch_flattened.c - While/switch flattening
# =============================================================================

WHILE_SWITCH_CASES = [
    DeobfuscationCase(
        function="while_switch_flattened",
        description="While(1)/switch dispatcher with ROL/XOR operations",
        project="example_libobfuscated.json",
        obfuscated_contains=["switch", "case"],
        must_change=True,
    ),
]


# =============================================================================
# Combined lists for different test scenarios
# =============================================================================

# All cases combined
ALL_CASES = (
    MANUALLY_OBFUSCATED_CASES
    + ABC_F6_CASES
    + ABC_XOR_CASES
    + APPROOV_CASES
    + CONSTANT_FOLDING_CASES
    + DISPATCHER_PATTERN_CASES
    + EXCEPTION_PATH_CASES
    + HODUR_CASES
    + NESTED_DISPATCHER_CASES
    + OLLVM_CASES
    + TIGRESS_CASES
    + UNWRAP_LOOPS_CASES
    + WHILE_SWITCH_CASES
)

# Core cases that must work (no exceptions/edge cases)
CORE_CASES = (
    MANUALLY_OBFUSCATED_CASES
    + TIGRESS_CASES
    + OLLVM_CASES
    + HODUR_CASES
    + WHILE_SWITCH_CASES
)

# Quick smoke test (fastest)
SMOKE_CASES = [
    c for c in ALL_CASES
    if c.function in {
        "test_chained_add",
        "test_xor",
        "test_or",
    }
]

# Cases that test unflattening rules
UNFLATTENING_CASES = (
    ABC_F6_CASES
    + ABC_XOR_CASES
    + APPROOV_CASES
    + DISPATCHER_PATTERN_CASES
    + NESTED_DISPATCHER_CASES
    + OLLVM_CASES
    + TIGRESS_CASES
)

# Cases that test instruction-level rules (MBA, constants)
INSTRUCTION_CASES = (
    MANUALLY_OBFUSCATED_CASES
    + CONSTANT_FOLDING_CASES
)

# Total function count
TOTAL_FUNCTION_COUNT = len(ALL_CASES)
