# Scanner Investigation: Why Refactored Rules Aren't Showing in Tests

## Problem Statement

The test `test_verify_refactored_modules_loaded` fails with:
```
AssertionError: 0 not greater than 0 - Should have refactored rules registered
```

## Investigation Results

### Scanner IS Working ✅

The scanner (`_Scanner.scan()`) uses `pkgutil.walk_packages()` which discovers **ALL** `.py` files in the package tree, including `*_refactored.py` files.

From `tests/system/ida_test_base.py:116-125`:
```python
import d810
from d810.reloadable import _Scanner
_Scanner.scan(
    package_path=d810.__path__,
    prefix="d810.",
    callback=None,
    skip_packages=False,
)
```

This DOES import the refactored modules:
- `rewrite_add_refactored.py`
- `rewrite_and_refactored.py`
- `rewrite_bnot_refactored.py`
- `rewrite_cst_refactored.py`
- `rewrite_mov_refactored.py`
- `rewrite_mul_refactored.py`
- `rewrite_neg_refactored.py`
- `rewrite_or_refactored.py`
- `rewrite_predicates_refactored.py`
- `rewrite_sub_refactored.py`
- `rewrite_xor_refactored.py`

### Rules ARE Registered ✅

When `Xor_HackersDelight1(VerifiableRule)` is defined:

**Class Hierarchy**:
```
Xor_HackersDelight1
  └─ VerifiableRule
      ├─ SymbolicRule
      └─ PatternMatchingRule
          └─ GenericPatternRule
              └─ InstructionOptimizationRule (Registrant is HERE)
                  ├─ OptimizationRule
                  └─ Registrant
```

**Registration Process**:
1. `Registrant.__init_subclass__()` is triggered
2. It walks up the class hierarchy looking for direct Registrant subclasses
3. It finds `InstructionOptimizationRule` (which has `Registrant in __bases__`)
4. It calls `InstructionOptimizationRule.register(Xor_HackersDelight1)`
5. Rule is added to `InstructionOptimizationRule.registry`

**Conclusion**: Refactored rules ARE registered, but in `InstructionOptimizationRule.registry`, NOT in `PatternMatchingRule.registry`.

## Root Causes of Test Failure

### Issue 1: Wrong Registry Method ❌

From `test_rule_tracking.py:293-296`:
```python
registered_rules = []
# Try to get rules from the registry
if hasattr(PatternMatchingRule, "get_all_rules"):
    registered_rules = PatternMatchingRule.get_all_rules()
```

**Problem**: `get_all_rules()` method doesn't exist!
- Grep results: "No matches found"
- This causes `registered_rules` to remain empty `[]`

**Should use**: Since `InstructionOptimizationRule` inherits from `Registrant`, it has:
- `Registrant.all()` - returns all registered subclasses
- `Registrant.get_subclasses(base)` - returns subclasses of a base type
- `Registrant.registry` - dict of all registered classes

### Issue 2: Wrong Class Name Pattern ❌

From `test_rule_tracking.py:303-305`:
```python
refactored_rules = [
    rule for rule in registered_rules if "Refactored" in rule.__name__
]
```

**Problem**: Refactored rule classes are NOT named with "Refactored" suffix!

**Actual Names** (from `rewrite_xor_refactored.py`):
- `Xor_HackersDelight1` (NOT `Xor_HackersDelight1Refactored`)
- `Xor_HackersDelight2`
- `Xor_MBA1`
- `Xor_Factor1`
- etc.

**Should check**: Whether the class is a subclass of `VerifiableRule`:
```python
from d810.optimizers.rules import VerifiableRule
refactored_rules = [
    rule for rule in registered_rules if issubclass(rule, VerifiableRule)
]
```

### Issue 3: Wrong Registry Location ❌

The test checks `PatternMatchingRule` registry, but rules are in `InstructionOptimizationRule` registry.

## The Fix

### Option A: Fix the Test (Recommended)

Update `test_verify_refactored_modules_loaded` to:

```python
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
```

### Option B: Add get_all_rules() Method

Add a convenience method to `PatternMatchingRule`:

```python
# In handler.py
class PatternMatchingRule(GenericPatternRule):
    # ... existing code ...

    @classmethod
    def get_all_rules(cls):
        """Get all registered pattern matching rules.

        Returns all InstructionOptimizationRule subclasses since
        PatternMatchingRule inherits from it.
        """
        from d810.optimizers.microcode.instructions.handler import InstructionOptimizationRule
        return InstructionOptimizationRule.all()
```

But this still wouldn't find VerifiableRule subclasses unless we also fix the "Refactored" name check.

## Recommendation

**Fix the test** (Option A) because:
1. It's more explicit about what it's checking
2. It uses the correct registry (`InstructionOptimizationRule.all()`)
3. It identifies refactored rules correctly (by checking `issubclass(rule, VerifiableRule)`)
4. It provides better diagnostic output

## Next Steps

1. ✅ Update `test_verify_refactored_modules_loaded` with the fixed implementation
2. ⏳ Commit and push changes
3. ⏳ Monitor CI run to verify test now passes
4. ⏳ Wire instrumentation to hexrays hooks (separate task)

## Files to Modify

- `tests/system/test_rule_tracking.py` - Fix `test_verify_refactored_modules_loaded`

## Expected Results

After fix:
- Test should report: "Total registered instruction optimization rules: ~50-100"
- Test should report: "Refactored (VerifiableRule) rules found: ~80-100" (20 rules × ~4-5 refactored modules)
- Test should PASS ✅

## Why This Matters

Once this test passes, it proves:
1. ✅ Scanner discovers `*_refactored.py` files
2. ✅ Refactored modules import successfully
3. ✅ VerifiableRule classes are defined
4. ✅ Rules register via Registrant metaclass
5. ✅ Rules appear in InstructionOptimizationRule registry

This unblocks:
- Verifying rules actually execute during deobfuscation
- Wiring instrumentation to track rule firings
- Measuring coverage of refactored code
