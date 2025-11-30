# CFG Modification Audit Report

**Date**: 2025-11-29
**Issue**: d810ng-jdz
**Branch**: cfg-audit-deferred-modifier

## Executive Summary

Audited 10 files for CFG modification patterns. Found:
- **3 files** use safe `DeferredGraphModifier` or abstraction patterns
- **2 files** are HIGH RISK with direct CFG modifications during iteration
- **5 files** use safe bounded patterns (single modification after analysis)

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
| `generic.py` | 🔴 High | Direct | **Needs refactor** |
| `unflattener_cf.py` | 🔴 High | Hybrid | **REMOVED** (redundant) |

## High-Risk Files Detail

### 1. `unflattener_cf.py` - REMOVED

**Status:** Removed as redundant. Other unflatteners (HodurUnflattener, UnflattenerSwitchCase) cover the same use cases with safer patterns.

### 2. `generic.py` - HIGH PRIORITY

**Problems:**
- Lines 735-736: `mba.insert_block()` called inside analysis loop
- Lines 814-820: Direct `predset._del()` / `succset.add_unique()` manipulation
- Lines 840-871: Multiple CFG modifications in loop without deferral

**Example of dangerous code:**
```python
for father_to_patch in fathers_to_patch_for_not_taken_branch:
    dup_blk, _ = duplicate_block(father_to_patch)  # Creates new block!
    make_2way_block_goto(father_to_patch, ...)     # Modifies CFG!
    update_blk_successor(dup_blk, ...)             # More modifications!
```

**Impact:** New blocks created during iteration can invalidate serial references.

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

### Phase 1: Document (This PR)
- [x] Complete audit of CFG modification patterns
- [x] Document safe vs unsafe patterns
- [x] Identify high-risk files

### Phase 2: Refactor unflattener_cf.py (Future PR)
- Complete the DeferredGraphModifier usage
- Move instruction copying outside of iteration loops
- Remove block serial assumptions

### Phase 3: Refactor generic.py (Future PR)
- Queue all block creation and edge changes
- Apply after analysis phase completes
- Add proper error handling for failed modifications

### Phase 4: Standardize (Future PR)
- Create coding guidelines for CFG modifications
- Add linter rules to detect direct CFG modification during iteration
- Consider making DeferredGraphModifier the standard API

## Files Analyzed

1. `src/d810/hexrays/deferred_modifier.py` - DeferredGraphModifier implementation
2. `src/d810/hexrays/cfg_utils.py` - Low-level CFG utilities
3. `src/d810/optimizers/microcode/flow/flattening/unflattener_hodur.py` - ✅ Safe
4. `src/d810/optimizers/microcode/flow/flattening/unflattener_cf.py` - 🔴 Unsafe
5. `src/d810/optimizers/microcode/flow/flattening/generic.py` - 🔴 Unsafe
6. `src/d810/optimizers/microcode/flow/flattening/services.py` - ✅ Safe
7. `src/d810/optimizers/microcode/flow/flattening/fix_pred_cond_jump_block.py` - ⚠️ Medium
8. `src/d810/optimizers/microcode/flow/flattening/unflattener_fake_jump.py` - ✅ Safe
9. `src/d810/optimizers/microcode/flow/jumps/handler.py` - ✅ Safe
10. `src/d810/optimizers/microcode/flow/loops/bogus_loops.py` - ✅ Safe
