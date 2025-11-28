# Plan: Fix Hodur Deflattening Bug

## Problem Statement
The `test_hodur_func` passes but produces semantically incorrect output. The deobfuscated code:
```c
void _hodur_func()
{
    for ( i = WinHttpOpen(&unk_9A68, 0, 0); ; WinHttpCloseHandle(i) )
        WinHttpConnect(i, &unk_9A90, 0x1BB, 0);
}
```

But the binary actually contains:
- 8 printf calls
- 6 resolve_api calls
- Multiple indirect function calls (function pointers)
- Complex state machine with 14 states

The deflattening removes almost all code, leaving only an infinite loop.

## Root Cause (CONFIRMED)

The `FixPredecessorOfConditionalJumpBlock` rule redirects ALL predecessors of block 9 (the main dispatcher), leaving block 9 with no predecessors:

```
Block 9: jnz state, 0xB2FD8FB6 (initial state check)
Predecessors: [8, 14, 19, 25, 30, 36, 41, 47, 54, 56, 62, 69, 71, 77, 82]

After rule analysis:
  Always taken (redirected to block 15): [14, 19, 25, 30, 36, 41, 47, 54, 56, 62, 69, 71, 77, 82]
  Never taken (redirected to block 10): [8]
  Remaining pointing to block 9: NONE
```

**The Problem**: When all predecessors are redirected:
1. Block 9 becomes unreachable (no predecessors)
2. IDA's optimizer removes block 9
3. This cascades - blocks 15, 20, 26, etc. (subsequent state checks) become unreachable
4. 94 out of 98 blocks are removed (96% reduction)

**Why This Happens**: The rule is designed for O-LLVM style flattening where:
- Each state handler loops back to a single dispatcher
- The dispatcher checks states in sequence
- Redirecting predecessors to skip checks is valid

But this creates a problem: If every predecessor of the dispatcher is redirected to skip it, the dispatcher becomes unreachable, taking all state handlers with it.

## Proposed Fix

### Option A: Keep Original Block Reachable (Recommended)
Modify `FixPredecessorOfConditionalJumpBlock.analyze_blk()` to ensure the original conditional block remains reachable:

```python
def analyze_blk(self, blk: ida_hexrays.mblock_t) -> int:
    # ... existing checks ...

    pred_jmp_always_taken, pred_jmp_never_taken, pred_jmp_unk = self.sort_predecessors(blk)

    # NEW: If ALL predecessors would be redirected, skip this block
    # to prevent making it unreachable
    total_preds = blk.npred()
    total_redirected = len(pred_jmp_always_taken) + len(pred_jmp_never_taken)
    if total_redirected == total_preds and total_preds > 0:
        unflat_logger.warning(
            f"Skipping block {blk.serial}: redirecting all {total_preds} "
            "predecessors would make block unreachable"
        )
        return 0

    # ... rest of patching logic ...
```

### Option B: Allow Full Redirect Only for True Unreachability
More aggressive approach that allows full redirect but validates:
- The successors remain reachable via alternative paths
- The state machine semantics are preserved

### Option C: Hodur-Specific Rule
Create a new rule `HodurUnflattener` that understands the nested-while pattern specifically, rather than relying on the generic O-LLVM unflattening rule.

## Implementation Plan

1. **Implement Option A** (safeguard against block becoming unreachable)
   - Modify `fix_pred_cond_jump_block.py:analyze_blk()`
   - Add check: if all predecessors would be redirected, skip patching this block

2. **Add semantic test assertions**
   - Test that deobfuscated code contains printf calls
   - Test that deobfuscated code contains resolve_api calls
   - Test that block count doesn't reduce by more than 50%

3. **Verify with test suite**
   - Run test_hodur_func with the fix
   - Ensure other O-LLVM tests still pass (they might rely on current behavior)

## Beads Issues
- `d810-ng-rxk`: Main bug - Investigate incorrect hodur deflattening
- `d810-ng-w8v`: Understand FixPredecessorOfConditionalJumpBlock state resolution
- `d810-ng-u2q`: Trace why valid code blocks become unreachable
- `d810-ng-4ar`: Add semantic correctness assertions to test_hodur_func

## Key Files
- `src/d810/optimizers/microcode/flow/flattening/fix_pred_cond_jump_block.py`
- `src/d810/hexrays/tracker.py` (MopTracker)
- `src/d810/optimizers/microcode/flow/flattening/utils.py` (get_all_possibles_values)
- `src/d810/expr/emulator.py` (MicroCodeInterpreter)

## Success Criteria
1. Deobfuscated `_hodur_func` contains printf calls
2. Deobfuscated `_hodur_func` contains resolve_api calls
3. All existing tests still pass
4. test_hodur_func has semantic correctness assertions
