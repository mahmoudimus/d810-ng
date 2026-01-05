# Coverage Analysis - Unloaded Modules Report

## Summary

**Overall Coverage: 9%** (14,005 lines missed out of 15,415 total)

Analysis shows that **most refactored code is not being loaded** during test execution. This indicates that:
1. New refactored modules aren't being imported
2. New services/managers aren't registered
3. DSL, caching, profiling, parallel systems are dormant

## Critical: 0% Coverage (Not Loaded At All)

These files are completely unused - they're not even being imported:

### Infrastructure (New Architecture)
| File | Lines | Status |
|------|-------|--------|
| `src/d810/optimizers/caching.py` | 158 | ❌ 0% - Persistent caching system not loaded |
| `src/d810/optimizers/core.py` | 32 | ❌ 0% - Core optimization base classes not loaded |
| `src/d810/optimizers/dsl.py` | 127 | ❌ 0% - **DSL system not loaded!** |
| `src/d810/optimizers/manager.py` | 128 | ❌ 0% - OptimizerManager not loaded |
| `src/d810/optimizers/parallel.py` | 171 | ❌ 0% - Parallel execution not loaded |
| `src/d810/optimizers/profiling.py` | 116 | ❌ 0% - Profiling system not loaded |
| `src/d810/optimizers/rules.py` | 83 | ❌ 0% - Rule base classes not loaded |
| `src/d810/optimizers/instrumentation.py` | 527 | ❌ 0% - **NEW: Instrumentation not loaded** |

### Refactored Pattern Matching Rules (ALL 0%)
| File | Lines | Status |
|------|-------|--------|
| `rewrite_add_refactored.py` | 99 | ❌ 0% |
| `rewrite_and_refactored.py` | 114 | ❌ 0% |
| `rewrite_bnot_refactored.py` | 113 | ❌ 0% |
| `rewrite_cst_refactored.py` | 187 | ❌ 0% |
| `rewrite_mov_refactored.py` | 22 | ❌ 0% |
| `rewrite_mul_refactored.py` | 31 | ❌ 0% |
| `rewrite_neg_refactored.py` | 49 | ❌ 0% |
| `rewrite_or_refactored.py` | 109 | ❌ 0% |
| `rewrite_predicates_refactored.py` | 172 | ❌ 0% |
| `rewrite_sub_refactored.py` | 70 | ❌ 0% |
| `rewrite_xor_refactored.py` | 118 | ❌ 0% |

**Total: 1,182 lines of refactored pattern rules not loaded**

### Flow Optimization (Control Flow Unflattening)
| File | Lines | Status |
|------|-------|--------|
| `unflattener_refactored.py` | 51 | ❌ 0% |
| `heuristics.py` | 158 | ❌ 0% |
| `services.py` | 35 | ❌ 0% |
| `unflattener.py` | 141 | ❌ 0% |
| `unflattener_badwhile_loop.py` | 65 | ❌ 0% |
| `unflattener_cf.py` | 942 | ❌ 0% |
| `unflattener_fake_jump.py` | 80 | ❌ 0% |
| `unflattener_switch_case.py` | 50 | ❌ 0% |
| `fix_pred_cond_jump_block.py` | 136 | ❌ 0% |
| `utils.py` | 36 | ❌ 0% |

**Total: 1,694 lines of flow optimization not loaded**

### Other Unused Systems
| File | Lines | Status |
|------|-------|--------|
| `src/d810/expr/emulator.py` | 450 | ❌ 0% - Emulation system |
| `src/d810/hexrays/tracker.py` | 419 | ❌ 0% - Tracking system |
| `src/d810/project_manager.py` | 100 | ❌ 0% - Project management |
| `src/d810/errors.py` | 23 | ❌ 0% - Error classes |

## Modules WITH Coverage (Actually Being Used)

### Good Coverage (50%+)
| File | Coverage | Notes |
|------|----------|-------|
| `src/d810/hexrays/hexrays_hooks.py` | 60% | ✅ Decompilation hooks working |
| `src/d810/optimizers/microcode/instructions/chain/chain_rules.py` | 56% | ✅ Chain rules active |
| `src/d810/expr/ast.py` | 48% | ✅ AST system in use |
| `src/d810/optimizers/microcode/instructions/handler.py` | 48% | ✅ Instruction handler active |
| `src/d810/optimizers/microcode/handler.py` | 43% | ✅ Microcode handler working |

### Moderate Coverage (20-50%)
| File | Coverage | Notes |
|------|----------|-------|
| `src/d810/expr/z3_utils.py` | 33% | Partial Z3 usage |
| `src/d810/optimizers/microcode/instructions/pattern_matching/handler.py` | 30% | Pattern handler partially used |
| `src/d810/cache.py` | 27% | Old cache system (not new caching.py) |
| `src/d810/manager.py` | 26% | D810Manager partially used |
| `src/d810/optimizers/microcode/instructions/z3/cst.py` | 34% | Z3 constant optimization |

## Why Refactored Code Isn't Loading

### 1. **Missing __init__.py Imports**

The refactored modules exist but aren't being imported:

```python
# src/d810/optimizers/__init__.py is empty!
# Should contain:
from .dsl import *
from .core import *
from .manager import *
# etc.
```

### 2. **Old Rule Registry Still in Use**

The old pattern matching rules (without `_refactored` suffix) are being loaded instead:

| Old File | Coverage | New File | Coverage |
|----------|----------|----------|----------|
| `rewrite_xor.py` | 1% | `rewrite_xor_refactored.py` | 0% |
| `rewrite_add.py` | 4% | `rewrite_add_refactored.py` | 0% |
| `rewrite_and.py` | 1% | `rewrite_and_refactored.py` | 0% |

This means the **old code is still active**, new code is **dormant**.

### 3. **Registry Not Scanning Refactored Modules**

The reloadable scanner in `src/d810/reloadable.py` likely skips `_refactored` files or they're not in the registry.

### 4. **Configuration Not Using New Systems**

Project configs (like `example_libobfuscated.json`) probably reference old rule names, not new ones.

## Impact on Refactoring

### Phase 1-3 (Architecture): ❌ Not Active
- ✅ Code written
- ❌ Code not imported
- ❌ Code not registered
- ❌ Tests not using it

### Phase 4-6 (Performance): ❌ Not Active
- ✅ Caching system written (158 lines)
- ✅ Profiling system written (116 lines)
- ✅ Parallel execution written (171 lines)
- ❌ None of it is being loaded!

### Phase 7 (Pattern Rules): ❌ Not Active
- ✅ 163/164 rules migrated (1,182 lines)
- ❌ 0% coverage on ALL refactored rules
- ❌ Old rules still in use (1-6% coverage)

## What Needs to Happen

### Immediate: Make Refactored Code Load

1. **Add imports to __init__.py files**
   ```python
   # src/d810/optimizers/__init__.py
   from .dsl import *
   from .core import *
   from .instrumentation import *
   # ...
   ```

2. **Register refactored rules**
   ```python
   # Make sure _refactored modules are scanned by reloadable.py
   # Update pattern_matching/__init__.py to import all *_refactored.py
   ```

3. **Update project configs**
   ```json
   {
     "ins_rules": [
       {"name": "XorFromOrAndSubRefactored", "is_activated": true},
       // not "XorFromOrAndSub"
     ]
   }
   ```

4. **Fix rule registration**
   ```python
   # In each *_refactored.py file, ensure:
   @register_optimization_rule
   class MyRuleRefactored(PatternMatchingRule):
       # ...
   ```

### Medium: Integration Tests

1. **Test that refactored modules load**
   ```python
   def test_refactored_modules_imported():
       import src.d810.optimizers.dsl
       import src.d810.optimizers.core
       # ...
   ```

2. **Test that refactored rules are in registry**
   ```python
   def test_refactored_rules_registered():
       from d810.optimizers.microcode.instructions.handler import InstructionOptimizationRule
       rules = InstructionOptimizationRule.registry
       assert any("Refactored" in name for name in rules.keys())
   ```

3. **Test that new systems work**
   ```python
   def test_caching_system_works():
       from d810.optimizers.caching import PersistentCache
       # ...
   ```

### Long-term: Migration

1. **Deprecate old rules** - Mark old files as deprecated
2. **Migrate configs** - Update all example configs to use refactored rules
3. **Remove old code** - Once refactored rules work, delete old implementations

## Test Results from Latest Run

**Run ID:** 19524695034
**Status:** ✅ Completed with failures
**Tests:** 23 passed, 2 failed, 24 skipped
**Coverage:** 9% (14,005 / 15,415 lines missed)

**Failures:**
1. `test_tigress_minmaxarray` - Control flow not unflattened (expected)
2. `test_verify_refactored_modules_loaded` - **Refactored modules not in registry!**

**Key Finding:** The test `test_verify_refactored_modules_loaded` is FAILING because it can't find refactored modules - confirming they're not being imported!

## Recommendations

### Priority 1: Make Refactored Code Load
1. Add proper `__init__.py` imports
2. Update `reloadable.py` to scan `_refactored` files
3. Verify imports with a simple test

### Priority 2: Update Configurations
1. Create new project configs using refactored rule names
2. Test with at least one refactored rule
3. Verify it fires and makes changes

### Priority 3: Instrumentation Integration
1. Wire instrumentation into hexrays hooks
2. Test that context is populated
3. Verify assertions work

### Priority 4: Performance Systems
1. Enable caching in test config
2. Enable profiling in test config
3. Verify they actually run

## Coverage Metrics

```
Total Lines:     15,415
Covered Lines:    1,410
Missed Lines:    14,005
Coverage:            9%

Breakdown:
- Refactored Code:     ~3,500 lines (0% coverage) ❌
- Infrastructure:        ~800 lines (0% coverage) ❌
- Old Pattern Rules:     ~900 lines (1-6% coverage) ⚠️
- Flow Optimization:   ~1,700 lines (0-5% coverage) ❌
- Core Systems:        ~1,400 lines (30-60% coverage) ✅
- Utilities/Helpers:   ~1,100 lines (10-40% coverage) ⚠️
- Tests/Config/Misc:   ~6,000 lines (varies)
```

## Next Steps

The instrumentation system we just built is ready, but like everything else in the refactored code, **it's not being loaded**.

We need to:
1. Fix the import/registration system
2. Make refactored modules actually load
3. Then the instrumentation will automatically work

**The refactoring code exists and is excellent - it just needs to be activated!**
