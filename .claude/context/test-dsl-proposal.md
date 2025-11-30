# Deobfuscation Test DSL Proposal

**Date**: 2025-11-29
**Status**: Draft
**Related**: tests/system/test_libdeobfuscated.py

## Problem Statement

The current test structure in `test_libdeobfuscated.py` has several issues:

1. **Boilerplate explosion** - Every test has 50+ lines of repetitive setup/teardown
2. **Inconsistent assertions** - Some tests check AST equivalence, some check string patterns, some check rule firing
3. **Project configuration scattered** - `state.for_project()` sometimes used, sometimes not
4. **Expected code duplicated** - Multi-line strings embedded in test code
5. **Stats verification copy-pasted** - Same 5-line pattern in every test
6. **Binary-specific handling ad-hoc** - No clean way to specify different expectations per binary

## Proposed Solutions

### Option 1: Decorator-based DSL

```python
from d810.testing import deobfuscation_test, DeobfuscationSpec

@deobfuscation_test(
    binary="libobfuscated",  # Resolves to .dll or .dylib
    function="test_chained_add",
    project="default_instruction_only.json",
)
class TestChainedAdd(DeobfuscationSpec):
    """Test simplification of chained addition expressions."""

    # What patterns indicate obfuscation (before d810)
    obfuscated_contains = ["0xFFFFFFEF"]

    # What the deobfuscated code should look like
    expected_code = """
        __int64 __fastcall test_chained_add(__int64 a1) {
            return 2 * a1[1] + 0x33;
        }
    """

    # Alternative acceptable patterns (if exact match fails)
    acceptable_patterns = [
        "2 * a1[1]",
        "a1[1] + a1[1]",
    ]

    # Rules that MUST fire
    required_rules = ["ArithmeticChain"]

    # Rules that SHOULD fire (warning if missing, not failure)
    expected_rules = ["Add_HackersDelightRule_1"]
```

**Pros**: Clean, readable, familiar pattern
**Cons**: Magic behavior, harder to debug

### Option 2: Data-driven with YAML/TOML

```yaml
# tests/system/specs/test_chained_add.yaml
binary: libobfuscated
function: test_chained_add
project: default_instruction_only.json

obfuscation:
  contains:
    - "0xFFFFFFEF"

deobfuscation:
  expected: |
    __int64 __fastcall test_chained_add(__int64 a1) {
        return 2 * a1[1] + 0x33;
    }
  acceptable_patterns:
    - "2 * a1[1]"
    - "a1[1] + a1[1]"

rules:
  required:
    - ArithmeticChain
  expected:
    - Add_HackersDelightRule_1

# Binary-specific overrides
overrides:
  libobfuscated.dll:
    obfuscation:
      contains:
        - "0xFFFFFFF1"  # Different constant on Windows
    rules:
      required:
        - ArithmeticChain
        - Z3ConstantOptimization
```

**Pros**: Non-programmers can edit, clean separation of data/code
**Cons**: Another file format, less type-safe, harder to debug

### Option 3: Dataclass + Parametrize (Recommended)

```python
from dataclasses import dataclass, field
from typing import Optional

@dataclass
class DeobfuscationCase:
    """Specification for a deobfuscation test case."""
    function: str
    project: str = "default_instruction_only.json"

    # Before assertions (obfuscated code)
    obfuscated_contains: list[str] = field(default_factory=list)
    obfuscated_not_contains: list[str] = field(default_factory=list)

    # After assertions (deobfuscated code)
    expected_code: Optional[str] = None
    acceptable_patterns: list[str] = field(default_factory=list)
    deobfuscated_not_contains: list[str] = field(default_factory=list)

    # Rule assertions
    required_rules: list[str] = field(default_factory=list)
    forbidden_rules: list[str] = field(default_factory=list)

    # Code change assertions
    must_change: bool = True
    min_simplification_ratio: float = 0.5  # lines_after / lines_before

    # Binary-specific overrides
    dll_overrides: Optional["DeobfuscationCase"] = None
    dylib_overrides: Optional["DeobfuscationCase"] = None


# Define all test cases as data
DEOBFUSCATION_CASES = [
    DeobfuscationCase(
        function="test_chained_add",
        obfuscated_contains=["0xFFFFFFEF"],
        expected_code="""
            __int64 __fastcall test_chained_add(__int64 a1) {
                return 2 * a1[1] + 0x33;
            }
        """,
        acceptable_patterns=["2 * a1[1]", "a1[1] + a1[1]"],
        required_rules=["ArithmeticChain"],
    ),
    DeobfuscationCase(
        function="test_cst_simplification",
        obfuscated_contains=["0x222E69C2", "0x50211120"],
        required_rules=["Z3ConstantOptimization"],
    ),
    DeobfuscationCase(
        function="constant_folding_test1",
        project="example_libobfuscated.json",
        obfuscated_contains=["__ROL"],
        required_rules=["FoldReadonlyDataRule"],
        must_change=True,
    ),
    DeobfuscationCase(
        function="ollvm_func",
        project="default_unflattening_ollvm.json",
        required_rules=["BnotOr_FactorRule_1"],
        # DLL fires different rules due to different microcode patterns
        dll_overrides=DeobfuscationCase(
            function="ollvm_func",
            required_rules=["Z3ConstantOptimization", "Z3setzRuleGeneric"],
        ),
    ),
]


# Single generic test function
@pytest.mark.parametrize("case", DEOBFUSCATION_CASES, ids=lambda c: c.function)
def test_deobfuscation(case: DeobfuscationCase, libobfuscated_setup, d810_state, ...):
    """Generic deobfuscation test runner."""
    run_deobfuscation_test(case, ...)
```

**Pros**:
- Type-safe with IDE autocomplete
- Pure Python, no new file formats
- Easy to extend with new assertion types
- Debuggable (breakpoints, inspection)
- Gradual migration (convert tests one at a time)

**Cons**:
- Still Python code (but minimal)

## Recommendation

**Option 3 (Dataclass + Parametrize)** is recommended because:

1. It provides the best balance of readability and type safety
2. The runner function would be ~50 lines handling all common patterns
3. Each test case becomes 5-10 lines of pure data
4. Binary-specific overrides are first-class citizens
5. Easy to add new assertion types without changing test structure

## Implementation Plan

1. Create `src/d810/testing/` package with:
   - `cases.py` - DeobfuscationCase dataclass
   - `runner.py` - run_deobfuscation_test() function
   - `assertions.py` - Helper assertion functions

2. Create `tests/system/cases/` directory with:
   - `libobfuscated.py` - All libobfuscated test cases as data
   - `hodur.py` - Hodur-specific test cases
   - etc.

3. Migrate tests incrementally:
   - Start with simplest tests (test_cst_simplification)
   - Move to more complex ones
   - Keep old tests working during migration

4. Add CLI tooling:
   - `pytest --generate-case test_foo` - Generate case from existing test
   - `pytest --validate-cases` - Check all cases have valid expectations

## Open Questions

1. Should expected_code be in separate files or inline?
2. How to handle tests that need custom setup (e.g., function renaming)?
3. Should we support test inheritance for common patterns?
4. How to handle flaky tests (timing, non-deterministic optimization)?
