# Hodur Profiling Results

**Date**: 2024-11-26
**Target**: `_hodur_func` in `libobfuscated.dylib`
**Rule**: `FixPredecessorOfConditionalJumpBlock`

## Summary

- **Total time**: 8.3 seconds for 124 changes in 2 passes
- **Recursive amplification**: 200 initial calls → 22,617 recursive `search_backward` calls (113x)
- **Object copies**: 1.4M `BlockInfo.get_copy` calls, 22K `MopHistory.get_copy` calls

## Top Bottlenecks (by total time in function)

| Function | Time | Calls | Issue |
|----------|------|-------|-------|
| `block_serial_path` | 1.324s | 102,657 | Property recomputed on every access |
| `MopHistory.get_copy` | 0.763s | 22,617 | Deep copy on every branch |
| `BlockInfo.get_copy` | 0.553s | 1,385,171 | Called from MopHistory |
| `minsn_t__print` | 0.405s | 25,388 | IDA formatting for logging |
| `str.format` | 0.312s | 234,847 | Logging overhead |

## Root Causes

### 1. Path Explosion (Primary)
`search_backward` recurses at every multi-predecessor block. With 15 predecessors at the dispatcher, this creates exponential paths:
- 200 initial calls from `sort_predecessors`
- 22,617 total recursive calls
- Each call creates a full copy of the tracker state

### 2. Excessive Copying
Every branch creates deep copies:
```python
def get_copy(self) -> MopHistory:
    new_mop_history.history = [x.get_copy() for x in self.history]  # O(n) per branch
```

### 3. Property Recomputation
`block_serial_path` is a property that creates a new list on every access:
```python
@property
def block_serial_path(self) -> list[int]:
    return [blk.serial for blk in self.block_path]  # Called 102K times!
```

### 4. Logging Overhead
~0.8s spent formatting strings for logging that may not even be displayed.

## Recommended Optimizations

### Quick Wins (Low effort, high impact)
1. **Cache `block_serial_path`** - invalidate on mutation
2. **Lazy logging** - use `logger.debug_on` guard before formatting
3. **Cache predecessor analysis results** - `(blk_serial, state_var) → values`

### Medium Effort
4. **Copy-on-write for MopHistory** - share history until mutation
5. **Immutable BlockInfo** - use tuples instead of mutable lists
6. **Result memoization** - `@functools.lru_cache` on `get_all_possibles_values`

### Algorithmic Improvements
7. **Dominator-based pruning** - skip paths that can't affect the state variable
8. **Abstract interpretation** - merge paths early, avoid concrete enumeration
9. **Incremental emulation** - checkpoint at branch points

## Files Generated

- `/tmp/hodur_profile.html` - Pyinstrument flame graph
- `/tmp/hodur_cprofile.prof` - cProfile binary stats (use `snakeviz` to view)
- `scripts/profile_unflattening.py` - Profiling script
