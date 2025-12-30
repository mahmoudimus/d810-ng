# Migration from RuleRegistry to Registrant

## Summary

The `RuleRegistry` class has been completely removed in favor of the existing `Registrant` metaclass system. This eliminates redundancy and provides a more powerful, standardized approach to managing optimization rules.

## What Changed

### Before (RuleRegistry)
```python
from d810.mba.rules import RuleRegistry, VerifiableRule, RULE_REGISTRY

# Manual registration with custom registry
my_registry = RuleRegistry("custom")

class MyRule(VerifiableRule, registry=my_registry):
    PATTERN = x + y
    REPLACEMENT = y + x

# Access via custom registry
for rule_cls in my_registry:
    print(rule_cls)

instances = my_registry.instantiate_all()
```

### After (Registrant)
```python
from d810.mba.rules import VerifiableRule
from d810.core.registry import Registrant

# Automatic registration - no manual steps needed!
class MyRule(VerifiableRule):
    PATTERN = x + y
    REPLACEMENT = y + x

# Access via VerifiableRule.registry
for rule_cls in VerifiableRule.registry.values():
    print(rule_cls)

instances = VerifiableRule.instantiate_all()
```

## Key Improvements

### 1. **Automatic Discovery**
Rules automatically register themselves when defined. No need for manual `register()` calls or passing `registry=` parameters.

### 2. **Hierarchical Scoping**
Create separate rule registries by defining intermediate base classes that also inherit from `Registrant`:

```python
class ArmRule(VerifiableRule, Registrant):
    """Base for ARM-specific rules - gets its own registry."""
    pass

class X86Rule(VerifiableRule, Registrant):
    """Base for X86-specific rules - gets its own registry."""
    pass

class ArmAdd(ArmRule):
    PATTERN = x + y
    REPLACEMENT = y + x

class X86Add(X86Rule):
    PATTERN = x - y
    REPLACEMENT = x + (-y)

# Each hierarchy has its own isolated registry
arm_rules = ArmRule.instantiate_all()      # Only ARM rules
x86_rules = X86Rule.instantiate_all()      # Only X86 rules
all_rules = VerifiableRule.instantiate_all()  # All rules
```

### 3. **Lazy Loading Support**
The `Registrant` system supports lazy loading of rule classes to avoid heavy imports:

```python
from functools import cache
from d810.mba.rules import VerifiableRule

@cache
def load_heavy_rule():
    # Import only when actually needed
    from rules.heavy_module import ComplexRule
    return ComplexRule

# Register the loader (not the class itself)
VerifiableRule.lazy_register(load_heavy_rule)

# Later, when optimization starts:
# This triggers lazy loading automatically
instances = VerifiableRule.instantiate_all()
```

### 4. **Standardization**
Uses the same registration pattern as other d810 components (optimizers, etc.), reducing cognitive load and making the codebase more consistent.

## Migration Guide

### For Rule Definitions

**No changes needed!** Rules that inherit from `VerifiableRule` automatically register.

Remove any `registry=` parameters if present:
```python
# Old
class MyRule(VerifiableRule, registry=my_registry):
    ...

# New
class MyRule(VerifiableRule):
    ...
```

### For Rule Access

Replace `RULE_REGISTRY` or custom registry instances with direct access to `VerifiableRule.registry`:

```python
# Old
from d810.mba.rules import RULE_REGISTRY

for rule_cls in RULE_REGISTRY:
    ...

instances = RULE_REGISTRY.instantiate_all()

# New
from d810.mba.rules import VerifiableRule

for rule_cls in VerifiableRule.registry.values():
    ...

instances = VerifiableRule.instantiate_all()
```

### For Custom Rule Hierarchies

Create intermediate base classes that inherit from both `VerifiableRule` and `Registrant`:

```python
# Old - separate registries required manual management
arm_registry = RuleRegistry("arm")
x86_registry = RuleRegistry("x86")

class ArmRule(VerifiableRule, registry=arm_registry):
    pass

# New - separate registries via inheritance
from d810.core.registry import Registrant

class ArmRule(VerifiableRule, Registrant):
    """Automatically gets its own registry."""
    pass

class X86Rule(VerifiableRule, Registrant):
    """Automatically gets its own registry."""
    pass
```

## Technical Details

### Registry Isolation

- Each direct subclass of `Registrant` gets its own `registry` and `lazy_registry` dictionaries
- Child classes register into their immediate Registrant-based parent
- `VerifiableRule` has its own registry that contains all rules
- Intermediate classes that also inherit `Registrant` get separate, isolated registries

### Registration Keys

Rules are registered using their class name (lowercased). If you need custom keys, set the `registrant_name` class variable:

```python
class MyRule(VerifiableRule):
    registrant_name = "custom_key"
    PATTERN = ...
```

### Filtering

The `Registrant` system provides powerful filtering capabilities:

```python
# Filter rules by predicate
non_abstract = VerifiableRule.filter(lambda cls: not inspect.isabstract(cls))

# Chain filters
from d810.optimizers.microcode.instructions.handler import PatternMatchingRule
pattern_rules = (
    VerifiableRule.filter(lambda cls: issubclass(cls, PatternMatchingRule))
                 .filter(lambda cls: cls.__name__.startswith("Xor_"))
)

# Iterate filtered results
for rule_cls in pattern_rules:
    print(rule_cls.__name__)
```

## Removed APIs

The following have been completely removed:

- `RuleRegistry` class
- `RULE_REGISTRY` global instance
- `registry=` parameter to `VerifiableRule`
- Manual `register()`, `unregister()`, `clear()` methods

## Benefits Summary

1. **Cleaner code**: No boilerplate registration code
2. **Type safety**: Rules are registered as classes, not strings
3. **Lazy loading**: Defer expensive imports until needed
4. **Hierarchical**: Organize rules by architecture/category automatically
5. **Discoverable**: `VerifiableRule.registry` is self-documenting
6. **Consistent**: Same pattern used across d810
7. **Thread-safe**: Registrant handles concurrent access properly
8. **Testable**: Easy to create isolated registries for unit tests
