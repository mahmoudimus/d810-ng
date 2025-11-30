# AST-Based Code Comparison for D810 Tests

This directory contains infrastructure for robust code comparison using libclang AST parsing, which is more reliable than string-based comparison for C/C++ code.

## Overview

Traditional string-based comparison of decompiled code is fragile because:
- Formatting differences (indentation, spacing)
- Type name variations (`int` vs `_DWORD`, `unsigned int` vs `DWORD`)
- Comment differences (IDA annotations, collapsed declarations)
- Equivalent but differently-formatted expressions

AST-based comparison solves these problems by comparing the **structural/semantic** representation of the code.

## Components

### 1. Clang Python Bindings (`clang/`)

The `clang/` directory contains Python bindings for libclang downloaded from the LLVM project:
- `cindex.py` - Main clang Python API
- `__init__.py` - Package initialization

### 2. Clang Initialization (`clang_init.py`)

Initializes libclang using the `libclang.so` from the IDA Pro installation:
```python
from .clang_init import get_clang_index

# Get the global clang index
index = get_clang_index()
```

### 3. Code Comparator (`code_comparator.py`)

Provides AST-based code comparison:
```python
from .code_comparator import CodeComparator

comparator = CodeComparator()
comparator.check_equivalence(actual_code, expected_code)
```

### 4. Test Mixin (`ast_test_mixin.py`)

Mixin class to add AST comparison to test classes:
```python
from .ast_test_mixin import ASTComparisonMixin
from .ida_test_base import IDAProTestCase

class MyTest(ASTComparisonMixin, IDAProTestCase):
    def test_something(self):
        actual = pseudocode_to_string(decompiled.get_pseudocode())
        expected = textwrap.dedent('''
            __int64 __fastcall func(int a1) {
                return a1 + 1;
            }
        ''')
        self.assertCodeEquivalent(actual, expected)
```

## Usage Examples

### Basic Comparison

```python
from .code_comparator import CodeComparator

comparator = CodeComparator()

actual = """
__int64 __fastcall test_xor(int a1, int a2, int *a4)
{
    *a4 = a2 ^ a1;
    return *a4;
}
"""

expected = """
__int64 __fastcall test_xor(int a1, int a2, int *a4)
{
    // Some comment that will be ignored

    *a4 = a2 ^ a1;
    return *a4;
}
"""

# This will pass - comments and whitespace are ignored
comparator.check_equivalence(actual, expected)
```

### Using the Test Mixin

```python
import textwrap
from .ast_test_mixin import ASTComparisonMixin
from .ida_test_base import IDAProTestCase

class TestDeobfuscation(ASTComparisonMixin, IDAProTestCase):
    binary_name = "libobfuscated.dll"

    def test_xor_simplification(self):
        func_ea = idc.get_name_ea_simple("test_xor")

        # Decompile with d810
        decompiled = idaapi.decompile(func_ea)
        actual = pseudocode_to_string(decompiled.get_pseudocode())

        expected = textwrap.dedent('''
            __int64 __fastcall test_xor(int a1, int a2, int *a4)
            {
                *a4 = a2 ^ a1;
                return *a4;
            }
        ''')

        # AST-based comparison - ignores formatting
        self.assertCodeEquivalent(actual, expected)
```

### Partial Matching

When you don't need exact equivalence, use pattern matching:

```python
def test_contains_simplified_xor(self):
    actual = get_decompiled_code(...)

    # Check that specific patterns exist
    self.assertCodeContains(
        actual,
        "a2 ^ a1",  # XOR should be simplified
        "return",   # Function should return
        msg="XOR pattern should be simplified"
    )

    # Check that obfuscation was removed
    self.assertCodeNotContains(
        actual,
        "2 * (a2 & a1)",  # Obfuscated XOR pattern
        msg="Obfuscated XOR should be removed"
    )
```

## Requirements

- libclang shared library (provided in IDA Pro Docker image at `/app/ida/libclang.so`)
- Python 3.6+

## Fallback Behavior

If libclang is not available, the `ASTComparisonMixin` automatically falls back to basic string comparison. Tests will still run, but may be more brittle to formatting changes.

## Benefits

1. **Robust**: Ignores formatting, comments, and minor syntactic variations
2. **Precise**: Detects real semantic differences
3. **Clear**: Failures show actual vs expected code
4. **Flexible**: Can use exact AST comparison or pattern matching
5. **Backward Compatible**: Falls back gracefully if libclang unavailable

## Limitations

1. **Requires libclang**: Must have libclang.so available
2. **Slower**: AST parsing is slower than string comparison (but still fast for tests)
3. **Debugging**: AST differences can be harder to debug than string differences

## Future Improvements

- Add AST diff visualization
- Support for comparing multiple functions
- Custom comparison rules for IDA-specific patterns
- Performance optimization with AST caching
