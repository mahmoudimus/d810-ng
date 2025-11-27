# Investigation: c_res mop=None in Constraint Evaluation System

## Problem Summary

When running system tests (`test_cst_simplification`, `test_constant_folding_1`), the decompiled code before and after D810 processing is **identical** - no optimizations are being applied despite rules loading correctly.

The error appearing repeatedly during decompilation:
```
ERROR - AstConstant(c_res) mop is None in create_mop for 0x60f6
```

## How to Reproduce

Run the failing system tests (requires IDA Pro with idapro module):

```bash
# Run specific failing tests
python -m pytest tests/system/test_libdeobfuscated.py::TestLibDeobfuscated::test_cst_simplification -v -s

python -m pytest tests/system/test_libdeobfuscated.py::TestLibDeobfuscated::test_constant_folding_1 -v -s

# Run both together
python -m pytest tests/system/test_libdeobfuscated.py::TestLibDeobfuscated::test_cst_simplification tests/system/test_libdeobfuscated.py::TestLibDeobfuscated::test_constant_folding_1 -v -s
```

## Test Environment

- Tests require `idapro` module (IDA Library for headless mode)
- Binary: `samples/bins/libobfuscated.dylib` (macOS) or `libobfuscated.dll` (Windows)
- Project config: `example_libobfuscated.json`

## Technical Analysis

### What's Working

1. **Rules are loading correctly**: 25 instruction rules, 10 block rules instantiated
2. **Import fixes applied**: `fold_rotatehelper.py` and `constant_call.py` now import correctly
3. **Unit tests pass**: All 199 unit tests pass

### What's Failing

The constraint-based rules in `src/d810/mba/rules/` use `c_res = Const("c_res")` to represent computed constant results. When these rules match a pattern, the `c_res` constant needs to have its `mop` attribute populated with the computed value, but it's ending up as `None`.

### Key Files

1. **Rule definitions** (where `c_res` is defined):
   - `src/d810/mba/rules/cst.py` - Multiple rules using `c_res`
   - `src/d810/mba/rules/and_.py:415` - `c_res = Const("c_res")`

2. **Where error occurs**:
   - `src/d810/speedups/expr/c_ast.pyx:670-678` (Cython version)
   - `src/d810/expr/p_ast.py:900-908` (Pure Python version)

   ```python
   if self.mop is None:
       logger.error(
           "%r mop is None in create_mop for 0x%x",
           self,
           ea,
       )
       raise AstEvaluationException(...)
   ```

3. **How c_res mop should be populated**:
   - `src/d810/optimizers/microcode/instructions/z3/cst.py:83`:
     ```python
     tmp.add_constant_leaf("c_res", val_0, tmp.mop.size)
     ```
   - This calls `add_constant_leaf` which creates a mop via `get_constant_mop()`

4. **IDA backend adapter**:
   - `src/d810/mba/backends/ida.py` - `IDAPatternAdapter` class
   - `_LeafWrapper` class for handling AstLeaf nodes

### Investigation Path

1. **Trace the constraint evaluation flow**:
   - How does a rule pattern get matched?
   - When does `c_res` get its value computed?
   - Why isn't the mop being populated?

2. **Check `add_constant_leaf` vs `AstConstant`**:
   - `add_constant_leaf()` creates an `AstLeaf` with a mop
   - But replacement patterns use `AstConstant("c_res")`
   - Is there a mismatch between what's stored and what's looked up?

3. **Look at `leafs_by_name` dictionary**:
   - When `add_constant_leaf("c_res", ...)` is called, it adds to `leafs_by_name`
   - When replacement is created, it looks up by name
   - The stored `AstLeaf` vs the `AstConstant` in replacement pattern might be the issue

4. **Enable debug logging for investigation**:
   ```python
   # In d810/expr/p_ast.py or c_ast.pyx, add:
   logger = getLogger(__name__, logging.DEBUG)
   ```

### Expected Behavior

When a rule like `ConstantFoldXorAnd_2` matches:
- Pattern: `(x ^ c_1) & c_2`
- Replacement: `(x & c_2) ^ c_res` where `c_res == c_1 & c_2`

The constraint `c_res == c_1 & c_2` should:
1. Compute the value from matched constants `c_1` and `c_2`
2. Create a mop for `c_res` with that computed value
3. Use that mop when generating the replacement instruction

### Actual Behavior

The `c_res` node ends up with `mop=None`, causing the replacement to fail and the original code to remain unchanged.

## Related Commits

Check git history for recent changes to:
- `src/d810/mba/backends/ida.py`
- `src/d810/expr/p_ast.py` / `c_ast.pyx`
- `src/d810/optimizers/microcode/instructions/z3/cst.py`

## Next Steps

1. Add debug logging to trace when `c_res` mop should be set
2. Check if the issue is in Cython version only or also Pure Python
3. Look for where constraint evaluation happens and verify mop assignment
4. Consider running tests with Cython disabled to isolate the issue
