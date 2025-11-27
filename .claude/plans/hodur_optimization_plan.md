# Hodur Unflattening Optimization Plan

**Epic**: d810-ng-7iq - Optimize hodur_func unflattening from 8.3s to <2s
**Current**: 6.2s (after Phase 1-2 optimizations)
**Target**: <2s (4x improvement from original)

## Analysis Summary

### Profiling Results (Nov 26, 2025)
| Bottleneck | Time | Calls | Root Cause |
|------------|------|-------|------------|
| `MopHistory.get_copy` | 0.52s | 22,617 | Deep copies on every branch |
| `BlockInfo.get_copy` | 0.47s | 1,385,171 | Called from MopHistory |
| `minsn_t__print` | 0.37s | 25,388 | IDA formatting for logging |
| `str.format` | 0.26s | 234,847 | Logging overhead |
| Generator expressions | 0.6s | - | Tuple/frozenset creation |

### Key Insight: Where Cython Helps vs Doesn't Help

Per `.cursorrules` guidelines:
- **DON'T Cythonize**: Hex-Rays object handling (`mop_t`, `minsn_t`, `mblock_t`)
- **DO Cythonize**: Pure algorithmic work (loops, maps, sets, arithmetic)

The current `BlockInfo` stores `mblock_t` references - we **cannot** Cythonize this directly. But we CAN:
1. Redesign to store only integers (serials, EAs)
2. Cythonize the numeric operations

## Implementation Plan

### Phase 3: Structural Sharing (d810-ng-8wb) - HIGH IMPACT
**Goal**: Eliminate 1.4M BlockInfo copies via immutable data structures

**Design**:
```python
# Current (mutable, requires deep copy)
class BlockInfo:
    blk: mblock_t        # IDA object - forces deep copy
    ins_list: list[minsn_t]

# New (immutable, shareable)
@dataclass(frozen=True, slots=True)
class ImmutableBlockInfo:
    blk_serial: int      # Just the serial number
    ins_ea_list: tuple[int, ...]  # Just EAs, not minsn_t objects
```

**Key Change**: Don't store IDA objects, store their numeric identifiers:
- `blk.serial` instead of `blk`
- `ins.ea` instead of `ins`
- Look up actual objects from `mba` only when needed (during emulation)

**Benchmark expectation**: 10-50x faster copy (tuple reference vs deep copy)

### Phase 4: Cython for Numeric Hot Paths (d810-ng-0rf) - MEDIUM IMPACT
**Goal**: Speed up remaining pure-Python numeric operations

**Candidates for Cythonization**:

1. **Serial tuple/frozenset generation** (0.6s in generators)
   ```cython
   # c_tracker.pyx
   cpdef tuple[int, ...] build_serial_tuple(list block_infos):
       cdef int n = len(block_infos)
       cdef int[:] result = np.empty(n, dtype=np.int32)
       cdef int i
       for i in range(n):
           result[i] = block_infos[i].blk_serial
       return tuple(result)
   ```

2. **`is_resolved()` loop** - checks if all mops have constant values
   ```cython
   cpdef bint is_resolved_fast(list unresolved_mops, dict constant_map):
       cdef int i, n = len(unresolved_mops)
       for i in range(n):
           if unresolved_mops[i] not in constant_map:
               return False
       return True
   ```

3. **Existing `hash_mop`** - already Cythonized in `_chexrays_api.pyx`

**Implementation**: Create `src/d810/speedups/hexrays/c_tracker.pyx` with:
- `build_serial_tuple()` - fast serial list generation
- `build_serial_frozenset()` - fast set generation
- `copy_block_info_list()` - fast list copy for immutable objects

### Phase 5: Lazy Logging (d810-ng-1q6) - MEDIUM IMPACT
**Goal**: Avoid 0.6s of string formatting when logging disabled

**Pattern**:
```python
# Before (always formats)
logger.debug("Checking block %d: %s", blk.serial, format_minsn_t(blk.tail))

# After (conditional format)
if logger.isEnabledFor(logging.DEBUG):
    logger.debug("Checking block %d: %s", blk.serial, format_minsn_t(blk.tail))
```

**Scope**: Update all logging in:
- `tracker.py` - main bottleneck
- `fix_pred_cond_jump_block.py`
- `emulator.py`

### Phase 6: Path Explosion Reduction (d810-ng-5pe) - HIGH IMPACT
**Goal**: Reduce 22K recursive calls via algorithmic improvement

**Options** (in order of complexity):
1. **Result memoization**: Cache `(blk_serial, state_var) → values` across calls
2. **Dominator-based pruning**: Skip paths that can't affect state variable
3. **Abstract interpretation**: Merge paths early, avoid concrete enumeration

**Start with memoization** - already partially implemented in V2 with `PredecessorAnalysisCache`

## Execution Order

```
Phase 3: Structural Sharing (d810-ng-8wb)
    ├── Most impactful, enables other optimizations
    └── Pure Python, no build complexity
          ↓
Phase 5: Lazy Logging (d810-ng-1q6)
    ├── Quick win, no dependencies
    └── ~0.6s savings
          ↓
Phase 4: Cython Numerics (d810-ng-0rf)
    ├── Requires Phase 3 (immutable BlockInfo)
    └── ~0.3-0.5s savings
          ↓
Phase 6: Path Explosion (d810-ng-5pe)
    ├── Most complex, highest potential
    └── Could reduce time by 50%+
```

## Expected Results

| Phase | Time After | Speedup |
|-------|-----------|---------|
| Current | 6.2s | baseline |
| Phase 3 (Structural) | ~4.0s | 1.5x |
| Phase 5 (Logging) | ~3.5s | 1.8x |
| Phase 4 (Cython) | ~3.0s | 2.1x |
| Phase 6 (Algorithm) | ~1.5s | 4.1x |

## Files to Modify/Create

**Modify**:
- `src/d810/hexrays/tracker.py` - Use immutable BlockInfo, lazy logging
- `src/d810/optimizers/microcode/flow/flattening/fix_pred_cond_jump_block.py` - Lazy logging

**Create**:
- `src/d810/speedups/hexrays/c_tracker.pyx` - Cython numeric operations
- `src/d810/speedups/hexrays/c_tracker.pxd` - Cython declarations

## Risks & Mitigations

1. **Risk**: Immutable BlockInfo breaks emulation that needs actual mblock_t
   - **Mitigation**: Keep mba reference in MopHistory, look up blocks by serial

2. **Risk**: Cython build complexity
   - **Mitigation**: Optional import with pure Python fallback

3. **Risk**: Algorithm changes break correctness
   - **Mitigation**: Run system tests before/after each change
