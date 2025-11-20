# Module Loading Implementation Status

## Summary

We're making the refactored code actually load and execute. The coverage analysis showed **0% coverage for all refactored modules**, meaning they weren't being imported at all.

## Changes Made (Current Commit)

### 1. Created `src/d810/optimizers/__init__.py`

**Purpose**: Ensure infrastructure modules are loaded when d810 starts.

```python
# Core infrastructure (must be imported first)
from . import dsl
from . import core
from . import rules

# Advanced features
from . import instrumentation
from . import caching
from . import profiling
from . import parallel
from . import manager

# Re-export commonly used classes
from .dsl import Var, Const, DynamicConst, when
from .core import OptimizationContext, OptimizationRule
from .rules import VerifiableRule
from .instrumentation import DeobfuscationContext
from .manager import OptimizerManager, create_default_manager
```

**Impact**:
- ✅ DSL system will load
- ✅ Instrumentation system will load
- ✅ Caching/profiling/parallel systems will load
- ✅ Makes infrastructure accessible to the rest of d810

### 2. Updated `src/d810/optimizers/rules.py`

**Purpose**: Bridge VerifiableRule to PatternMatchingRule's registry.

**Changes**:
- Added lazy import of PatternMatchingRule to avoid circular dependencies
- Modified `__init_subclass__` to register VerifiableRule subclasses with both:
  1. RULE_REGISTRY (for testing/verification)
  2. PatternMatchingRule.registry (for D810 plugin discovery)

**Code**:
```python
def _get_pattern_matching_rule():
    """Lazy import of PatternMatchingRule to avoid circular dependencies."""
    global _PatternMatchingRule
    if _PatternMatchingRule is None:
        try:
            from d810.optimizers.microcode.instructions.pattern_matching.handler import PatternMatchingRule
            _PatternMatchingRule = PatternMatchingRule
        except ImportError:
            _PatternMatchingRule = object
    return _PatternMatchingRule

# In __init_subclass__:
PatternMatchingRuleBase = _get_pattern_matching_rule()
if PatternMatchingRuleBase is not None and PatternMatchingRuleBase is not object:
    if hasattr(PatternMatchingRuleBase, 'register'):
        PatternMatchingRuleBase.register(cls)
```

**Impact**:
- ✅ Refactored rules (VerifiableRule subclasses) will register with D810
- ✅ D810Manager will find them in `InstructionOptimizationRule.registry`
- ⚠️ **May need testing** - depends on when import happens

### 3. Simplified `pattern_matching/__init__.py`

**Purpose**: Clarify that rules are scanned, not explicitly imported.

**Before**: Empty file (just docstring)
**After**: Documents scanning behavior, imports only base classes

```python
"""Pattern matching optimizer handlers.

Rules in this module are automatically discovered and registered by the
reloadable scanner. Both old (ast-based) and refactored (DSL-based) rules
are registered automatically when their modules are imported.
"""

from .handler import PatternMatchingRule, GenericPatternRule
```

**Impact**:
- ✅ Clear documentation of how rules are loaded
- ✅ Imports minimal dependencies for type checking
- ✅ Doesn't force premature imports

### 4. Created `test_imports.py`

**Purpose**: Diagnostic tool to verify module loading.

**Features**:
- Tests if infrastructure modules can be imported
- Tests if refactored rule modules can be imported
- Checks InstructionOptimizationRule.registry for registered rules
- Checks RULE_REGISTRY for VerifiableRule instances
- Reports success/failure for each module

**Usage**:
```bash
# Outside IDA (will fail on ida_hexrays imports)
PYTHONPATH=./src python3 test_imports.py

# Inside IDA
/path/to/ida/idat64 -A -S"test_imports.py"
```

## What Should Happen Now

### Expected Improvements in Next CI Run:

1. **Infrastructure Modules** (should go from 0% → some coverage):
   - `src/d810/optimizers/dsl.py`
   - `src/d810/optimizers/core.py`
   - `src/d810/optimizers/rules.py`
   - `src/d810/optimizers/instrumentation.py`

2. **Refactored Pattern Rules** (should go from 0% → some coverage):
   - `rewrite_xor_refactored.py`
   - `rewrite_and_refactored.py`
   - `rewrite_or_refactored.py`
   - ... (all 11 refactored rule files)

3. **Test Results**:
   - `test_verify_refactored_modules_loaded` should PASS
   - Some refactored rules should appear in registry

## What Still Needs to Be Done

### Critical: Make VerifiableRule Work with D810

**The Problem**:
- VerifiableRule doesn't inherit from PatternMatchingRule
- PatternMatchingRule has AST-based pattern matching
- VerifiableRule has DSL-based pattern matching
- They need different `apply()` implementations

**The Solution Options**:

#### Option A: Multiple Inheritance (Complex)
```python
class VerifiableRule(SymbolicRule, PatternMatchingRule):
    # Needs to reconcile different apply() signatures
    ...
```
**Pros**: Rules automatically register
**Cons**: Complex inheritance, method conflicts

#### Option B: Adapter Pattern (Clean)
```python
class VerifiableRuleAdapter(PatternMatchingRule):
    """Wraps a VerifiableRule to work with D810's pattern matching."""
    def __init__(self, verifiable_rule):
        self.wrapped = verifiable_rule

    def apply(self, context, ins):
        # Translate DSL pattern to AST pattern
        # Call wrapped rule's matching logic
        ...
```
**Pros**: Clean separation, no inheritance conflicts
**Cons**: Needs manual wrapping, extra layer

#### Option C: Unified Base Class (Best Long-term)
```python
class PatternRule(InstructionOptimizationRule):
    """Base for both AST and DSL pattern rules."""

    @abc.abstractmethod
    def matches(self, ins): ...

    @abc.abstractmethod
    def transform(self, ins, match): ...

    def apply(self, context, ins):
        if match := self.matches(ins):
            return self.transform(ins, match)
        return 0
```
**Pros**: Clean architecture, works for both old and new
**Cons**: Requires refactoring PatternMatchingRule

**Recommended**: Start with Option B (adapter), migrate to Option C later.

### Medium Priority: Wire Instrumentation

**File**: `src/d810/hexrays/hexrays_hooks.py`

**What to Add**:
```python
def apply_rule(self, rule, context, element):
    """Apply a rule and record in instrumentation."""
    changes = rule.apply(context, element)

    # Record in deobfuscation context if available
    if hasattr(self.manager, '_deobfuscation_context'):
        ctx = self.manager._deobfuscation_context
        if ctx:
            rule_type = self._infer_rule_type(rule)
            if rule_type == "flow":
                ctx.record_flow_rule_execution(
                    rule_name=rule.name,
                    changes=changes,
                    maturity=context.maturity,
                )
            elif rule_type == "pattern":
                ctx.record_pattern_rule_execution(
                    rule_name=rule.name,
                    changes=changes,
                    maturity=context.maturity,
                    pattern_type=self._infer_pattern_type(rule),
                )
            else:
                ctx.record_rule_execution(
                    rule_name=rule.name,
                    rule_type="instruction",
                    changes=changes,
                    maturity=context.maturity,
                )

    return changes
```

### Low Priority: Enable Caching/Profiling/Parallel

**These modules are now imported**, but not actively used. To enable them:

1. **Caching**: Update project configs to enable persistent cache
   ```json
   {
     "additional_configuration": {
       "enable_persistent_cache": true,
       "cache_db_path": "~/.d810/cache.db"
     }
   }
   ```

2. **Profiling**: Already enabled via D810Manager.profiler
   - Just needs to be wired into apply_rule()

3. **Parallel**: Update manager to use parallel executor
   ```python
   from d810.optimizers.parallel import ParallelExecutor
   executor = ParallelExecutor(num_workers=4)
   results = executor.map(apply_rule, rules)
   ```

## Testing Plan

### 1. Verify Module Loading (Immediate)
```bash
# Wait for CI to complete
# Check coverage report for improvements
```

**Expected**: Coverage for refactored files should increase from 0% to 10-30%

### 2. Verify Rule Registration (Next)
```python
def test_refactored_rules_registered():
    from d810.optimizers.microcode.instructions.handler import InstructionOptimizationRule

    # Check for refactored rules
    refactored_rules = [
        name for name in InstructionOptimizationRule.registry.keys()
        if "Xor_HackersDelight" in name or "Xor_MBA" in name
    ]

    assert len(refactored_rules) > 0, "No refactored rules found in registry"
```

### 3. Verify Rules Fire (Final)
```python
def test_refactored_rules_fire():
    """Test that refactored rules actually optimize code."""
    ctx = get_current_deobfuscation_context()

    # Decompile test_xor function
    ...

    # Check that refactored XOR rules fired
    assert ctx.pattern_matches_by_type("xor") > 0
    assert ctx.rule_fired("Xor_HackersDelight1")
```

## Success Criteria

### Phase 1: Loading (Current)
- ✅ Infrastructure modules importable
- ✅ Refactored rule modules importable
- ⏳ Coverage shows modules are loaded
- ⏳ test_verify_refactored_modules_loaded passes

### Phase 2: Registration (Next)
- ⏳ VerifiableRule subclasses in InstructionOptimizationRule.registry
- ⏳ D810Manager finds refactored rules
- ⏳ test_refactored_rules_registered passes

### Phase 3: Execution (Final)
- ⏳ Refactored rules actually fire during deobfuscation
- ⏳ Instrumentation records rule executions
- ⏳ Coverage shows rules being used (>30%)
- ⏳ Test functions are successfully deobfuscated

## Next Steps

1. **Wait for CI** - Check if module loading helped coverage
2. **Implement Adapter** - Create VerifiableRuleAdapter to bridge DSL and AST patterns
3. **Wire Instrumentation** - Connect DeobfuscationContext to hexrays hooks
4. **Test Rule Firing** - Verify refactored rules actually optimize code
5. **Enable Performance Features** - Turn on caching, profiling, parallel execution

## Timeline

- **Now**: Modules are being loaded (commit 2e59e72)
- **Next 30min**: CI results show coverage improvement
- **Next 2hrs**: Implement adapter, wire instrumentation
- **Next 4hrs**: Full test suite passing with refactored rules
- **Next 8hrs**: Deprecate old rules, migrate all configs

## Current Status

📊 **Coverage**: 9% → Waiting for CI results (expecting 15-25%)
🔄 **Module Loading**: ✅ Implemented, ⏳ Testing
🔗 **Rule Registration**: ⚠️ Partial (needs adapter)
⚡ **Rule Execution**: ❌ Not yet implemented
📈 **Instrumentation**: ✅ Created, ❌ Not wired
🎯 **Performance**: ✅ Created, ❌ Not enabled

**Overall Progress**: Making refactored code load → Making it register → Making it execute
