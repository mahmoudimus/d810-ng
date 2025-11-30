# Refactored Rules Not Registering - Investigation

## Problem
Refactored DSL-based rules (Ver

ifiableRule subclasses) are not appearing in d810's rule registry, even though:
- Modules ARE being imported (all in sys.modules)
- VerifiableRule now inherits from PatternMatchingRule
- No metaclass conflicts (Registry inherits from ABCMeta)

## Current Status

### What Works ✅
1. Module import: All `rewrite_*_refactored.py` modules load successfully  
2. Metaclass resolution: Registry(ABCMeta) resolves conflicts cleanly
3. Old rules work: `Xor_HackersDelightRule_1`, etc. from `rewrite_xor.py` execute fine

### What Doesn't Work ❌
1. **Zero refactored rules in registry**: `PatternMatchingRule.get_all_rules()` returns 0
2. Old rules are used instead: `Xor_HackersDelightRule_3` executes, not `Xor_HackersDelight3`
3. Test `test_verify_refactored_modules_loaded` fails: "0 not greater than 0"

## Root Cause Hypothesis

The issue is likely in how `Registrant.__init_subclass__` works:

```python
def __init_subclass__(cls):
    # Register *cls* into every immediate parent that is itself a Registrant
    for base in cls.__bases__:
        if Registrant in base.__bases__:  # Only DIRECT subclasses
            base.register(cls)
```

When `Xor_HackersDelight1(VerifiableRule)` is created:
- VerifiableRule is the immediate parent
- But VerifiableRule is NOT a direct subclass of Registrant (it's indirect via PatternMatchingRule)
- So it doesn't have its own registry
- The rule should register into InstructionOptimizationRule's registry (which IS a direct subclass)

But the test checks `PatternMatchingRule`'s registry, which may be empty!

## Next Steps

1. **Verify registry location**: Check if rules are in InstructionOptimizationRule.registry vs PatternMatchingRule.registry
2. **Check `get_all_rules()`**: See if it traverses the class hierarchy properly
3. **Fix test or fix registration**: Either update test to look in right place, or make VerifiableRule a direct subclass of Registrant
4. **Alternative**: Make VerifiableRule directly inherit from Registrant to get its own registry

## Files Modified

- `src/d810/optimizers/rules.py`: Made VerifiableRule inherit from PatternMatchingRule
- Multiple inheritance: `VerifiableRule(SymbolicRule, PatternMatchingRule)`
- __init_subclass__ captures PATTERN/REPLACEMENT and renames to _dsl_pattern/_dsl_replacement

## Test Results

Run 19525565485:
- 23 tests passed
- 7 tests failed (same as before)
- Still using old rules, not refactored ones
