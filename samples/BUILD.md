# Building libobfuscated.dll

## Problem

The current `libobfuscated.dll` in this repository was built **without exporting function names**.

This causes all tests in `test_libdeobfuscated.py` to fail because IDA Pro cannot find functions by their expected names (`test_cst_simplification`, `test_chained_add`, etc.). Instead, IDA only sees generic names like `sub_180001000`.

## Solution

The source files have been updated with `EXPORT` macros to properly export function names. However, **the DLL must be rebuilt on Windows** for these changes to take effect.

## Building on Windows

### Prerequisites

- Visual Studio or MinGW-w64 compiler
- Windows SDK
- Make (optional, can use compiler directly)

### Using the Makefile (Cross-compilation or native)

```bash
cd samples
make clean
BINARY_NAME=libobfuscated make
```

This will create `bins/libobfuscated.dll` with properly exported function names.

### Verify Exports

After building, verify the exports using:

```cmd
dumpbin /EXPORTS bins\libobfuscated.dll
```

You should see:
```
    ordinal hint RVA      name
          1    0 00001000 test_and
          2    1 00001050 test_chained_add
          3    2 000010A0 test_cst_simplification
          4    3 000010F0 test_mba_guessing
          5    4 00001140 test_neg
          6    5 00001190 test_opaque_predicate
          7    6 000011E0 test_or
          8    7 00001230 test_xor
          9    8 00001280 tigress_minmaxarray
```

### Alternative: Using Visual Studio directly

```cmd
cl /LD /O0 /Zi /Iinclude ^
   src/c/manually_obfuscated.c ^
   src/c/tigress_obfuscated.c ^
   src/c/constant_folding.c ^
   src/c/ollvm_obfuscated.c ^
   src/c/unwrap_loops.c ^
   src/c/while_switch_flattened.c ^
   /Fe:bins/libobfuscated.dll
```

## Why This Matters

Without exported function names:
- ❌ IDA Pro cannot find test functions by name
- ❌ All `test_libdeobfuscated.py` tests fail with "Function 'xxx' not found"
- ❌ Tests that rely on specific function names cannot run

With exported function names:
- ✅ IDA Pro can find functions by their source names
- ✅ All tests can locate and decompile the correct functions
- ✅ Test suite can verify deobfuscation results

## Current Status

- **Source files**: ✅ Updated with EXPORT macros
- **DLL binary**: ❌ Needs to be rebuilt on Windows
- **Tests**: ❌ Will fail until DLL is rebuilt

## Next Steps

1. Rebuild `libobfuscated.dll` on a Windows machine
2. Commit the updated DLL to the repository
3. Verify tests pass in GitHub Actions
