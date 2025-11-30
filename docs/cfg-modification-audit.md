# CFG Modification Audit Report

**Date**: 2025-11-29
**Issue**: d810ng-jdz
**Branch**: cfg-audit-deferred-modifier

## Executive Summary

Audited 10 files for CFG modification patterns. Found:
- **4 files** use safe `DeferredGraphModifier` or abstraction patterns
- **1 file** was HIGH RISK, now removed (unflattener_cf.py was redundant)
- **5 files** use safe bounded patterns (single modification after analysis)

**Update 2025-11-29**: `generic.py` has been refactored to use `ABCBlockSplitter`
for deferred CFG modifications. The ABC pattern handling now follows the safe
deferred pattern instead of immediate recursive modifications.

**Update 2025-11-29 (part 2)**: `resolve_dispatcher_father()` in `generic.py` has been
migrated to use `DeferredGraphModifier` for deferred CFG modifications. This completes
the migration of all CFG modification paths in `generic.py` to the deferred pattern:
- `fix_fathers_from_mop_history()` → `ABCBlockSplitter`
- `resolve_dispatcher_father()` → `DeferredGraphModifier`

## Risk Assessment

| File | Risk | Pattern | Action |
|------|------|---------|--------|
| `unflattener_hodur.py` | ✅ Safe | Deferred | Reference implementation |
| `services.py` | ✅ Safe | Abstracted | Reference implementation |
| `unflattener_fake_jump.py` | ✅ Safe | Bounded | No change needed |
| `bogus_loops.py` | ✅ Safe | Bounded | No change needed |
| `stackvars_constprop.py` | ✅ Safe | Data-flow | No change needed |
| `tracker.py` | ✅ Safe | Analysis | No change needed |
| `handler.py` | ✅ Safe | Analysis | No change needed |
| `fix_pred_cond_jump_block.py` | ⚠️ Medium | Direct+Cache | Consider refactor |
| `generic.py` | ✅ Safe | Deferred | **REFACTORED** (uses ABCBlockSplitter) |
| `unflattener_cf.py` | 🔴 High | Hybrid | **REMOVED** (redundant) |

## High-Risk Files Detail

### 1. `unflattener_cf.py` - REMOVED

**Status:** Removed as redundant. Other unflatteners (HodurUnflattener, UnflattenerSwitchCase) cover the same use cases with safer patterns.

### 2. `generic.py` - FULLY REFACTORED ✅

**Status:** All CFG modification paths now use deferred patterns.

**Solution (Part 1 - ABC patterns):**
- Created `abc_block_splitter.py` with the `ABCBlockSplitter` class
- `fix_fathers_from_mop_history()` now delegates to `ABCBlockSplitter`
- Analysis phase: collect all ABC split operations without modifying CFG
- Apply phase: perform all splits atomically after analysis completes

**Solution (Part 2 - Dispatcher resolution):**
- Extended `DeferredGraphModifier` with `BLOCK_CREATE_WITH_REDIRECT` modification type
- `resolve_dispatcher_father()` now accepts optional `deferred_modifier` parameter
- `remove_flattening()` creates a `DeferredGraphModifier` and applies after all resolutions
- Block creation and goto changes are queued during analysis, applied atomically afterward

**Before (dangerous):**
```python
# Immediate CFG modification during iteration
for block in father_history.block_path:
    total_n += self.father_history_patcher_abc(block)  # Modifies CFG immediately!
```

**After (safe):**
```python
# Deferred CFG modification
splitter = ABCBlockSplitter(self.mba)
for father_history in father_histories:
    for block in father_history.block_path:
        splitter.analyze_block(block)  # Only collects, no modifications
total_n = splitter.apply()  # All modifications applied atomically
```

**Legacy code retained:** The original `father_patcher_abc_*` functions are kept for
reference but are no longer called from the main code path.

## Safe Patterns (Reference)

### Pattern 1: DeferredGraphModifier (unflattener_hodur.py)

```python
# During analysis - queue changes only
for blk in blocks:
    if should_redirect(blk):
        self.deferred.queue_goto_change(blk.serial, new_target)

# After analysis - apply all changes atomically
self.deferred.apply(run_optimize_local=True)
```

### Pattern 2: Abstraction Layer (services.py)

```python
# Each operation is self-contained and atomic
CFGPatcher.redirect_edge(context, from_block, to_block)
CFGPatcher.duplicate_block(context, block)
CFGPatcher.insert_intermediate_block(context, pred, succ)
```

### Pattern 3: Bounded Single Modification (unflattener_fake_jump.py)

```python
# Analyze first (no modifications)
target_info = analyze_predecessors(blk)

# Single modification after analysis
change_1way_block_successor(blk, target_info.new_target)
```

## Recommendations

### Phase 1: Document ✅ COMPLETE
- [x] Complete audit of CFG modification patterns
- [x] Document safe vs unsafe patterns
- [x] Identify high-risk files

### Phase 2: Remove unflattener_cf.py ✅ COMPLETE
- [x] Removed as redundant with other unflatteners
- [x] Removed flatfold-noswitch.json config

### Phase 3: Refactor generic.py ✅ COMPLETE
- [x] Created ABCBlockSplitter for deferred pattern
- [x] Queue all block creation and edge changes
- [x] Apply after analysis phase completes
- [x] Added proper error handling for failed modifications

### Phase 4: Standardize (Future PR)
- Create coding guidelines for CFG modifications
- Add linter rules to detect direct CFG modification during iteration
- Consider making DeferredGraphModifier the standard API

## Files Analyzed

1. `src/d810/hexrays/deferred_modifier.py` - DeferredGraphModifier implementation
2. `src/d810/hexrays/cfg_utils.py` - Low-level CFG utilities
3. `src/d810/optimizers/microcode/flow/flattening/unflattener_hodur.py` - ✅ Safe
4. `src/d810/optimizers/microcode/flow/flattening/unflattener_cf.py` - **REMOVED**
5. `src/d810/optimizers/microcode/flow/flattening/generic.py` - ✅ Safe (refactored)
6. `src/d810/optimizers/microcode/flow/flattening/abc_block_splitter.py` - ✅ Safe (new)
7. `src/d810/optimizers/microcode/flow/flattening/services.py` - ✅ Safe
8. `src/d810/optimizers/microcode/flow/flattening/fix_pred_cond_jump_block.py` - ⚠️ Medium
9. `src/d810/optimizers/microcode/flow/flattening/unflattener_fake_jump.py` - ✅ Safe
10. `src/d810/optimizers/microcode/flow/jumps/handler.py` - ✅ Safe
11. `src/d810/optimizers/microcode/flow/loops/bogus_loops.py` - ✅ Safe
