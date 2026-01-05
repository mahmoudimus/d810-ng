# Structural Deobfuscation Testing with Instrumentation

This guide explains how to write robust, maintainable tests for d810 deobfuscation using the instrumentation system.

## Problem: Brittle String-Based Tests

Traditional deobfuscation tests check the final pseudocode output using string matching:

```python
def test_xor_old_way(self):
    # Decompile with d810
    code = get_decompiled_code()

    # Brittle assertion: exact string match
    expected = "return (a2 ^ a1) + (a3 ^ a1);"
    self.assertEqual(code, expected)  # FAILS if IDA changes formatting!
```

**Problems:**
- **Fragile**: Breaks when IDA changes indentation, type names, or formatting
- **Unclear**: Doesn't explain *why* the code should look this way
- **Limited**: Can't verify *how* deobfuscation happened, only the final result

## Solution: Structural Assertions with Instrumentation

Instead of checking string output, we assert **structural properties** of the deobfuscation:

```python
from .stutils import d810_state, get_current_deobfuscation_context
from .deobfuscation_assertions import (
    assert_deobfuscation_improved_code,
    assert_pattern_simplified,
    assert_total_changes,
)

def test_xor_structural(self):
    with d810_state() as state:
        # Decompile with d810
        state.start_d810()
        decompiled = idaapi.decompile(func_ea)

        # Get instrumentation context
        ctx = get_current_deobfuscation_context()

        # Structural assertions
        assert_deobfuscation_improved_code(ctx)
        assert_pattern_simplified(ctx, "xor", min_count=2)
        assert_total_changes(ctx, min_changes=5)
```

**Benefits:**
- **Robust**: Independent of formatting changes
- **Clear**: Explains what deobfuscation should achieve
- **Detailed**: Verifies the optimization process, not just the result

## What the Instrumentation Tracks

The `DeobfuscationContext` captures comprehensive optimization data:

### Rule Execution
- Which rules fired
- How many times each rule fired
- How many changes each rule made
- Execution order of rules

### CFG Transformations
- Blocks added/removed
- Edges redirected
- Switch cases before/after (control flow flattening)
- Dispatchers found

### Pattern Matching
- XOR patterns simplified
- AND/OR patterns simplified
- NEG patterns simplified
- MBA patterns simplified
- Constants folded

## Available Assertions

### High-Level Assertions

```python
# Assert that deobfuscation actually improved the code
assert_deobfuscation_improved_code(ctx)

# Assert total changes are within expected range
assert_total_changes(ctx, min_changes=10, max_changes=50)
```

### Rule Assertions

```python
# Assert a specific rule fired
assert_rule_fired(ctx, "UnflattenerTigress")

# Assert a rule fired an exact number of times
assert_rule_fire_count(ctx, "XorFromOrAndSub", expected_count=5)

# Assert a rule made minimum changes
assert_minimum_changes(ctx, "Add_HackersDelight1", min_changes=3)

# Assert a rule did NOT fire
assert_rule_not_fired(ctx, "UnwantedRule")
```

### Flow Optimization Assertions

```python
# Assert control flow unflattening occurred
assert_unflattening_occurred(ctx, min_edges=10)

# Assert edges were redirected
assert_edges_redirected(ctx, min_count=15)

# Assert switch cases were reduced
assert_switch_cases_reduced(ctx, min_reduction=10)

# Assert at least one flow rule fired
assert_flow_rule_fired(ctx)
```

### Pattern Matching Assertions

```python
# Assert specific pattern types were simplified
assert_pattern_simplified(ctx, "xor", min_count=5)
assert_pattern_simplified(ctx, "and", min_count=3)
assert_pattern_simplified(ctx, "mba", min_count=2)
assert_pattern_simplified(ctx, "constant", min_count=10)
```

## Complete Example

Here's a complete test showing the full workflow:

```python
import logging
import unittest

import idaapi
import idc

from .ida_test_base import IDAProTestCase
from .stutils import (
    d810_state,
    get_current_deobfuscation_context,
    pseudocode_to_string,
)
from .deobfuscation_assertions import (
    assert_deobfuscation_improved_code,
    assert_unflattening_occurred,
    assert_edges_redirected,
    assert_switch_cases_reduced,
    get_deobfuscation_summary,
)

logger = logging.getLogger(__name__)


class TestTigressUnflattening(IDAProTestCase):
    binary_name = "libobfuscated.dll"

    def test_tigress_minmaxarray_structural(self):
        """Test Tigress control flow flattening removal."""
        func_ea = idc.get_name_ea_simple("tigress_minmaxarray")
        self.assertNotEqual(func_ea, idaapi.BADADDR)

        with d810_state() as state:
            # Configure for Tigress unflattening
            with state.for_project("example_libobfuscated.json"):
                # BEFORE: Decompile without d810
                state.stop_d810()
                before = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
                code_before = pseudocode_to_string(before.get_pseudocode())

                # Count switch cases before
                cases_before = code_before.count("case ")

                # AFTER: Decompile with d810
                state.start_d810()
                after = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
                code_after = pseudocode_to_string(after.get_pseudocode())

                # Count switch cases after
                cases_after = code_after.count("case ")

            # Get instrumentation context
            ctx = get_current_deobfuscation_context()

            # Print detailed summary for debugging
            logger.info("\n" + get_deobfuscation_summary(ctx))

            # STRUCTURAL ASSERTIONS

            # 1. Verify deobfuscation occurred
            assert_deobfuscation_improved_code(ctx)

            # 2. Verify unflattening specifically
            assert_unflattening_occurred(ctx, min_edges=10)

            # 3. Verify CFG was modified
            assert_edges_redirected(ctx, min_count=10)

            # 4. Verify switch cases were reduced
            assert_switch_cases_reduced(ctx, min_reduction=5)

            # 5. Traditional assertion still works
            self.assertLess(
                cases_after,
                cases_before,
                f"Switch cases should be reduced ({cases_before} → {cases_after})"
            )

            # 6. Verify we got natural control flow back
            self.assertGreater(
                code_after.count("for (") + code_after.count("if ("),
                0,
                "Unflattened code should have natural control flow"
            )
```

## Debugging with Instrumentation

The instrumentation provides rich debugging output:

```python
def test_debug_example(self):
    with d810_state() as state:
        state.start_d810()
        decompiled = idaapi.decompile(func_ea)

        ctx = get_current_deobfuscation_context()

        # Print summary for debugging
        print(get_deobfuscation_summary(ctx))

        # Or access raw data
        summary = ctx.get_summary()
        print(f"Total rules fired: {len(ctx.rules_fired)}")
        print(f"Total changes: {ctx.total_changes()}")

        # Inspect individual executions
        for exec in ctx.executions:
            print(f"{exec.rule_name}: {exec.changes_made} changes")

        # Check specific patterns
        xor_count = ctx.pattern_matches_by_type("xor")
        print(f"XOR patterns simplified: {xor_count}")
```

## Migration Guide

To migrate existing tests:

### Before (String-Based)
```python
def test_xor(self):
    code = decompile_with_d810(func)
    expected = "return a ^ b;"
    self.assertEqual(code.strip(), expected.strip())  # Brittle!
```

### After (Structural)
```python
def test_xor(self):
    with d810_state() as state:
        state.start_d810()
        decompiled = idaapi.decompile(func_ea)
        code = pseudocode_to_string(decompiled.get_pseudocode())

        ctx = get_current_deobfuscation_context()

        # Structural: What should happen
        assert_pattern_simplified(ctx, "xor", min_count=1)
        assert_total_changes(ctx, min_changes=1)

        # Still can check output if needed
        self.assertIn("^", code, "XOR operator should appear")
```

## Best Practices

1. **Use structural assertions first**: They're more robust than string matching

2. **Print summaries during development**: Use `get_deobfuscation_summary()` to understand what's happening

3. **Combine approaches**: Use structural assertions for process verification, string checks for output validation

4. **Be specific about expectations**: Assert the minimum required, not exact values
   - ✅ `assert_pattern_simplified(ctx, "xor", min_count=1)`
   - ❌ `assert_rule_fire_count(ctx, "XorRule", expected_count=23)`  # Too brittle

5. **Document why**: Explain what obfuscation pattern you're testing
   ```python
   # This function has 3 XOR patterns obfuscated as (a|b) - (a&b)
   # The XorFromOrAndSub rule should simplify all 3
   assert_pattern_simplified(ctx, "xor", min_count=3)
   ```

## Implementation Details

The instrumentation system consists of:

### Core Components

1. **`DeobfuscationContext`** (`src/d810/optimizers/instrumentation.py`)
   - Tracks all optimization activity
   - Provides query methods for tests

2. **Assertion Helpers** (`tests/system/deobfuscation_assertions.py`)
   - High-level assertions for common checks
   - Helpful error messages

3. **Test Utilities** (`tests/system/stutils.py`)
   - `d810_state()` context manager
   - `get_current_deobfuscation_context()` accessor

### Data Flow

```
Test Start
   ↓
d810_state() creates DeobfuscationContext
   ↓
D810Manager._deobfuscation_context = ctx
   ↓
During optimization, manager calls:
   ctx.record_rule_execution(...)
   ctx.record_flow_rule_execution(...)
   ctx.record_pattern_rule_execution(...)
   ↓
Test accesses ctx via get_current_deobfuscation_context()
   ↓
Test makes structural assertions
```

## See Also

- `tests/system/test_structural_deobfuscation.py` - Complete examples
- `src/d810/optimizers/instrumentation.py` - Instrumentation implementation
- `tests/system/deobfuscation_assertions.py` - Available assertions
