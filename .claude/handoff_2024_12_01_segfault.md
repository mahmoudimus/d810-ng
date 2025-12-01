# D810-NG Segfault Investigation Handoff - December 1, 2024

## Branch
`cfg-audit-deferred-modifier`

## Current Issue: d810ng-6kg (P3)
**IDA segfault on `test_tigress_minmaxarray`**

### What We Know

1. **The segfault occurs during D810 processing** - not a pure IDA bug
   - Without D810: `tigress_minmaxarray` decompiles successfully
   - With D810: Segfault in `ida_hexrays.decompile_func`

2. **Not Cython related (probably)** - We started investigating if Cython was the cause
   - Added env var support to `CythonMode` in `src/d810/core/cymode.py`
   - BUT: The Cython modules are imported at module load time, before `CythonMode` is checked
   - The `CythonMode.is_enabled()` flag exists but nothing actually checks it!

3. **The crash happens in isolation** - not accumulated state from previous tests

### Files Modified (uncommitted)
- `src/d810/core/cymode.py` - Added `D810_NO_CYTHON` env var support to `CythonMode`

### Next Steps to Complete Cython Disable

The modules that import Cython don't check `CythonMode.is_enabled()`. Options:

**Option A: Check env var directly in each module** (simpler)
Update these files to check `os.environ.get("D810_NO_CYTHON")` at import time:
- `src/d810/expr/ast.py`
- `src/d810/hexrays/block_helpers.py`
- `src/d810/hexrays/hexrays_helpers.py:149`
- `src/d810/hexrays/tracker_components.py:151`
- `src/d810/expr/emulator.py:22-23`
- `src/d810/optimizers/microcode/flow/constant_prop/_fast_dataflow.py:5`

**Option B: Use lazy imports** (cleaner but more complex)
Wrap all Cython imports in functions that check `CythonMode.is_enabled()` at call time.

### How to Test

```bash
# With Cython (should crash)
PYTHONPATH=src pytest "tests/system/test_libdeobfuscated.py::TestLibDeobfuscated::test_tigress_minmaxarray" -v

# Without D810 (should pass)
PYTHONPATH=src python -c "
import idapro
idapro.open_database('samples/bins/libobfuscated.dylib', True)
import idaapi, idc
ea = idc.get_name_ea_simple('_tigress_minmaxarray')
cfunc = idaapi.decompile(ea, flags=idaapi.DECOMP_NO_CACHE)
print(f'Success: {cfunc is not None}')
idapro.close_database(False)
"

# Once D810_NO_CYTHON is working:
D810_NO_CYTHON=1 PYTHONPATH=src pytest "tests/system/test_libdeobfuscated.py::TestLibDeobfuscated::test_tigress_minmaxarray" -v
```

### If Not Cython-Related

The segfault could be caused by:
1. CFG manipulation (insert_block, copy_block, etc.) corrupting IDA state
2. Holding references to IDA objects that get invalidated
3. A specific optimization rule that doesn't handle this function correctly

To investigate further:
1. Disable rules one by one to find the culprit
2. Add more verbose logging to track which rule is running when it crashes
3. Check if the function has unusual characteristics (size, complexity, loops)

### Commands

```bash
# Check current beads status
bd show d810ng-6kg

# Run all unit tests (should pass)
PYTHONPATH=src pytest tests/unit/ -v

# Run the crashing test
PYTHONPATH=src pytest "tests/system/test_libdeobfuscated.py::TestLibDeobfuscated::test_tigress_minmaxarray" -v
```

### Session Summary

This session fixed:
- **d810ng-d7x** (P1): `ValueError: ast is None` in z3_utils.py - FIXED
- **d810ng-0fu** (P2): ABC pattern test failures - FIXED

Remaining:
- **d810ng-6kg** (P3): IDA segfault - IN PROGRESS (investigating Cython)
