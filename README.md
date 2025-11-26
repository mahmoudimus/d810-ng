# Introduction

## What is D-810 ng

D-810 ng (Next Generation) is an IDA Pro plugin which can be used to deobfuscate code at decompilation time by modifying IDA Pro microcode.
It was designed with the following goals in mind:

* It should have as least as possible impact on our standard reverse engineering workflow
  * Fully integrated to IDA Pro
* It should be easily extensible and configurable
  * Fast creation of new deobfuscation rules
  * Configurable so that we don't have to modify the source code to use rules for a specific project
* Performance impact should be reasonable
  * Our goal is to be transparent for the reverse engineer
  * But we don't care if the decompilation of a function takes 1 more second if the resulting code is much simpler.

## Installation

**Only IDA v9 or later is supported with Python 3.10 and higher** (since we need the microcode Python API)

Copy the contents of this repository to `.idapro/plugins` or `%appdata%\Hex-Rays\IDA pro\plugins`.

It is recommended to install Z3 to be able to use several features of D-810:

```bash
pip3 install z3-solver
```

## Building with Cython Performance Optimizations

D-810 ng includes optional Cython-accelerated modules for performance-critical code paths. The plugin works in pure Python mode without building, but you can optionally compile the Cython extensions for better performance.

### Quick Start: Pure Python (No Build)

The plugin works out-of-the-box without any compilation:

```bash
pip install -e .
```

### Installation Profiles

```bash
# Development: testing, coverage, vendoring tool
pip install -e ".[dev]"

# CI: testing only (no vendoring tool needed)
pip install -e ".[ci]"

# Profiling: pyinstrument for performance analysis
pip install -e ".[profiling]"

# Speedups: Cython for performance improvements
pip install -e ".[speedups]"

# Combine as needed:
pip install -e ".[dev,profiling]"
```

D-810 automatically detects if Cython speedups are available and falls back to pure Python implementations if not.

### Building Cython Extensions

To build with performance optimizations:

#### Requirements

* **Python**: 3.10 or higher
* **Cython**: 3.0.0 or higher
* **setuptools**: 77.0.1 or higher
* **IDA SDK**: For full Hex-Rays integration (set via `IDA_SDK` environment variable)

#### Standard Build

```bash
# Install with Cython speedups
pip install -e .[speedups]

# Or build explicitly
IDA_SDK=/path/to/idasdk python setup.py build_ext --inplace
```

#### Debug Build

For development with debug symbols and profiling:

```bash
DEBUG=1 IDA_SDK=/path/to/idasdk python setup.py build_ext --inplace
```

This enables:

* Debug symbols (`-g`, `-ggdb`)
* Line tracing for profiling
* Coverage support
* Assertions enabled

#### Creating Debug Symbols (macOS)

On macOS, use `dsymutil` to create `.dSYM` bundles for debugging:

```bash
# Create debug symbols for all compiled modules
fd --glob "**/*.so" "./src/d810/speedups" --exclude "*.dSYM" -x dsymutil -o '{.}.so.dSYM' '{}'
```

### Compiled Modules

When built, the following Cython modules are compiled:

* `d810.speedups.cythxr._chexrays_api` - Hex-Rays API Cython wrappers
* `d810.speedups.expr.c_ast` - AST core functionality
* `d810.speedups.expr.c_ast_evaluate` - Fast AST evaluator
* `d810.speedups.optimizers.microcode.flow.constant_prop.c_dataflow` - Fast dataflow analysis
* `d810.speedups.optimizers.microcode.flow.constant_prop.c_stackvars_constprop` - Stack variable constant propagation

### Platform-Specific Notes

#### macOS

```bash
# Set minimum macOS version (automatically configured)
# Requires macOS 10.9+
# ARM64 builds supported on Apple Silicon
# x86_64 builds supported on Intel Macs

IDA_SDK=/path/to/idasdk python setup.py build_ext --inplace
```

#### Linux

```bash
# Builds with GCC
# Suppresses IDA SDK-specific warnings automatically

IDA_SDK=/path/to/idasdk python setup.py build_ext --inplace
```

#### Windows

```bash
# Builds with MSVC
# Uses /TP for C++ mode and /EHa for exception handling

set IDA_SDK=C:\path\to\idasdk
python setup.py build_ext --inplace
```

### Verifying Cython Mode

Check if Cython speedups are loaded:

```python
from d810.expr.ast import _USING_CYTHON
print(f"Cython enabled: {_USING_CYTHON}")
```

### Performance Benchmarks

Run the Cython vs Pure Python benchmarks inside IDA:

```bash
pytest tests/system/test_cython_benchmark.py -v -s
```

**Benchmark Results** (Apple M1 Pro, IDA 9.2, Python 3.13):

| Benchmark | Cython | Pure Python | Speedup |
|-----------|--------|-------------|---------|
| AST Node Creation (1000 iter) | 2.1 ms | 2.3 ms | ~1.1x |
| AST Clone (500 iter) | 2.1 ms | 2.4 ms | **1.2x** |
| AST Get Pattern (500 iter) | 1.0 ms | 1.0 ms | ~1.0x |
| AST Get Leaf List (500 iter) | 0.3 ms | 0.2 ms | 0.7x |

> **Note**: Results vary by hardware and IDA version. The current Cython implementations focus on hot paths in the decompilation pipeline. AST operations show modest gains due to Python object overhead. Run the benchmark yourself with `pytest tests/system/test_cython_benchmark.py -v -s`.

### GitHub Actions CI/CD

The repository includes automated wheel building for distribution. See `.github/workflows/build-cython.yml` for the CI/CD pipeline that builds platform-specific wheels for:

* **Linux**: x86_64 (Ubuntu latest)
* **macOS**: x86_64 (Intel) and ARM64 (Apple Silicon)
* **Windows**: x86_64

**Python versions**: 3.10, 3.11, 3.12, 3.13

For more details, see [`docs/BUILDING.md`](docs/BUILDING.md).

## Using D-810 ng

* Load the plugin by using the `Ctrl-Shift-D` shortcut, you should see this configuration GUI

!["Configuration Gui"](./docs/source/images/gui_plugin_configuration.png "Configuration GUI")

* Choose or create your project configuration
  * If you are not sure what to do here, leave *default_instruction_only.json*.
* Click on the `Start` button to enable deobfuscation
* Decompile an obfuscated function, the code should be simplified (hopefully)
* When you want to disable deobfuscation, just click on the `Stop` button.

### Test Runner

D-810 ng comes with a built-in test runner that automatically loads system tests from the tests folder, under `tests/system`. This GUI is a simple test runner that allows a developer to run tests *inside* of IDA Pro, accessing the hexrays decompiler API and utilizing specific samples under `samples/bins` to test transformations.

The test runner is self-explanatory:

!["Test Runner Example"](./docs/source/images/test_runner_example-01.png "Test Runner Example")

Test reloading exists without needing to restart `IDA Pro` and you can execute different part of the tests via the testing context menu:

!["Test Runner Context Menu"](./docs/source/images/test_runner_example-ctx-menu.png "Test Runner Context Menu")

## Adding New Deobfuscation Rules

D-810 ng uses a modern, declarative DSL for defining optimization rules. Rules are automatically registered, tested with Z3, and integrated into the deobfuscation pipeline.

### Quick Start: Create a Simple Rule

```python
from d810.mba.rules import VerifiableRule
from d810.mba.dsl import Var, Const

# Define symbolic variables
x, y = Var("x_0"), Var("x_1")

class MySimpleRule(VerifiableRule):
    """Simplify: (x | y) - (x & y) => x ^ y

    This is a standard bitwise identity.
    """

    PATTERN = (x | y) - (x & y)
    REPLACEMENT = x ^ y

    DESCRIPTION = "Simplify OR-AND pattern to XOR"
    REFERENCE = "Hacker's Delight, Chapter 2"
```

**That's it!** Your rule is now:

* ✅ Automatically registered with d810
* ✅ Automatically tested with Z3 to prove correctness
* ✅ Ready to use in deobfuscation

### Rule with Constraints

For rules that require additional conditions:

```python
class MyConstrainedRule(VerifiableRule):
    """Simplify: (x ^ c1) + 2*(x & c2) => x + c1 where c1 == c2"""

    c_1 = Const("c_1")
    c_2 = Const("c_2")

    PATTERN = (x ^ c_1) + 2 * (x & c_2)
    REPLACEMENT = x + c_1

    # Declarative constraint - automatically converted to Z3
    CONSTRAINTS = [c_1 == c_2]

    DESCRIPTION = "Simplify XOR-AND with equal constants"
```

### Rule with Dynamic Constants

For constants computed from matched values:

```python
class MyDynamicRule(VerifiableRule):
    """Simplify: (x & c1) | ((x & c2) ^ c3) => (x & c_res) ^ c_xor_res"""

    c_and_1 = Const("c_and_1")
    c_and_2 = Const("c_and_2")
    c_xor = Const("c_xor")
    c_and_res = Const("c_and_res")  # c_and_1 | c_and_2
    c_xor_res = Const("c_xor_res")  # c_and_1 ^ c_xor

    PATTERN = (x & c_and_1) | ((x & c_and_2) ^ c_xor)
    REPLACEMENT = (x & c_and_res) ^ c_xor_res

    CONSTRAINTS = [
        # Masks must be disjoint
        (c_and_1 & c_and_2) == 0,
        # Define result constants
        c_and_res == c_and_1 | c_and_2,
        c_xor_res == c_and_1 ^ c_xor,
    ]

    DESCRIPTION = "OLLVM obfuscation pattern"
```

### Advanced: Custom Z3 Constraints

For rules with BIT_WIDTH-dependent constraints:

```python
class MyAdvancedRule(VerifiableRule):
    """Simplify: (x >> c1) >> c2 => x >> (c1 + c2)"""

    c_1 = Const("c_1")
    c_2 = Const("c_2")
    c_res = Const("c_res")

    PATTERN = (x >> c_1) >> c_2
    REPLACEMENT = x >> c_res

    CONSTRAINTS = [
        c_res == c_1 + c_2  # Declarative for runtime
    ]

    def get_constraints(self, z3_vars):
        """Override to add BIT_WIDTH-specific Z3 constraints."""
        import z3

        base = super().get_constraints(z3_vars)

        return base + [
            # Check for overflow
            z3.And(
                z3.ULT(z3_vars["c_1"], z3_vars["c_1"] + z3_vars["c_2"]),
                z3.ULT(z3_vars["c_2"], z3_vars["c_1"] + z3_vars["c_2"])
            ),
            # Check sum is within bounds
            z3.ULT(z3_vars["c_1"] + z3_vars["c_2"], self.BIT_WIDTH),
        ]
```

### Predicate Rules: Boolean-to-Integer Conversion

For rules that work with comparisons (predicates), use `.to_int()` to convert boolean results to integers:

```python
class MyPredicateRule(VerifiableRule):
    """Simplify: (x | c1) != c2 => 1 (when c1 | c2 != c2)

    If (c1 | c2) != c2, then c1 has bits that c2 doesn't have.
    Therefore (x | c1) can never equal c2, so the comparison is always true.
    """

    c1, c2 = Const("c_1"), Const("c_2")

    # Capture the FULL comparison using .to_int()
    # This bridges boolean constraints to integer results (0 or 1)
    PATTERN = ((x | c1) != c2).to_int()

    # Declarative constraint
    CONSTRAINTS = [(c1 | c2) != c2]

    # Result: 1 (comparison is always true)
    REPLACEMENT = ONE
```

**Key insight**: Comparisons like `!=`, `==`, `<`, `>` return `ConstraintExpr` (boolean formulas). Use `.to_int()` to convert them to `SymbolicExpression` (0 or 1), maintaining type safety.

### Extension Operations: Zero-Extend (Zext)

For rules involving zero-extension (IDA's `xdu` instruction):

```python
from d810.mba.dsl import Var, Const, Zext
from d810.mba.rules import VerifiableRule

class MyZextRule(VerifiableRule):
    """Simplify: Zext(x & 1, 32) == 2 => 0

    Zero-extending (x & 1) to 32 bits produces either 0 or 1.
    Since neither equals 2, the comparison is always false.
    """

    # Pattern: Zext(x & 1, 32) == 2
    PATTERN = (Zext(x & ONE, 32) == TWO).to_int()

    # Result: 0 (always false)
    REPLACEMENT = ZERO
```

**Note**: `Zext(expr, target_width)` creates a zero-extension operation that:

* Converts to Z3's `ZeroExt` for verification
* Maps to IDA's `M_XDU` opcode for pattern matching

### Bit-Width-Specific Verification

Some rules are only valid for specific bit-widths (e.g., byte operations where 256 wraps to 0). Instead of marking these as `SKIP_VERIFICATION`, you can **configure the verification bit-width**:

```python
from d810.mba.dsl import Var, Const, ZERO
from d810.mba.rules import VerifiableRule

class Xor_Hodur_2(VerifiableRule):
    """Simplify: (x - c_0) ^ (y ^ c_1) => (x + c_1) ^ (y ^ c_1) when c_0 + c_1 = 256

    BYTE-SPECIFIC: This rule uses 8-bit Z3 bitvectors for verification.
    In byte arithmetic: -c_0 ≡ c_1 (mod 256) when c_0 + c_1 = 256
    """

    # Configure Z3 to use 8-bit bitvectors instead of default 32-bit
    BIT_WIDTH = 8

    c_0 = Const("c_0")
    c_1 = Const("c_1")

    PATTERN = (x - c_0) ^ (y ^ c_1)
    REPLACEMENT = (x + c_1) ^ (y ^ c_1)

    def get_constraints(self, z3_vars):
        """Custom constraint: c_0 + c_1 == 0 in 8-bit arithmetic.

        At 8-bit width, 256 wraps to 0, so c_0 + c_1 == 0 means they sum to 256.
        """
        import z3

        if "c_0" not in z3_vars or "c_1" not in z3_vars:
            return []

        # In 8-bit: 256 ≡ 0 (mod 256)
        return [z3_vars["c_0"] + z3_vars["c_1"] == z3.BitVecVal(0, 8)]

    def check_candidate(self, candidate):
        """Runtime check: verify c_0 + c_1 == 256 with actual values.

        Z3 uses 8-bit arithmetic, but IDA provides actual constant values.
        """
        if (candidate["c_0"].value is None) or (candidate["c_1"].value is None):
            return False
        return (candidate["c_0"].value + candidate["c_1"].value) == 256
```

**Key points:**

* **`BIT_WIDTH = 8`**: Tells Z3 to create 8-bit bitvectors instead of 32-bit
* **`get_constraints()`**: Override to provide explicit Z3 constraints that account for overflow
* **`check_candidate()`**: Runtime validation with actual constant values from IDA
* **Why this works**: In 8-bit arithmetic, `256 ≡ 0 (mod 256)`, so `c_0 + c_1 = 256` becomes `c_0 + c_1 = 0`

**Common bit-widths:**

* `BIT_WIDTH = 8` - Byte operations (0-255, 256 wraps to 0)
* `BIT_WIDTH = 16` - Word operations (0-65535, 65536 wraps to 0)
* `BIT_WIDTH = 32` - Default for most rules (0-4294967295)

This approach is preferable to `SKIP_VERIFICATION` because:

* ✅ Z3 still verifies mathematical correctness at the appropriate bit-width
* ✅ Catches subtle bugs that might only appear in byte/word operations
* ✅ Documents the size-specific nature of the rule explicitly

### Context-Aware Rules (Advanced)

Some rules need to inspect or modify the instruction context beyond just the source operands. The **context-aware DSL** provides declarative helpers for these advanced cases without requiring direct manipulation of IDA's internal API.

**Use cases:**

* Rules that only apply to specific destination types (registers, memory, high-half registers)
* Rules that need to bind values from the instruction context (parent register, operand size)
* Rules that modify the destination operand (e.g., changing from high-half to full register)

#### Example: Fix IDA's constant propagation for high-half register writes

```python
from d810.mba.dsl import Const, Var
from d810.mba.rules import VerifiableRule
from d810.optimizers.extensions import context, when

c_0 = Const("c_0")
full_reg = Var("full_reg")

class ReplaceMovHighContext(VerifiableRule):
    """Transform: mov #c, rX^2 → mov (#c << 16) | (rX & 0xFFFF), rX

    IDA doesn't propagate constants through high-half register writes.
    This rule fixes that by writing to the full register instead.
    """

    # Pattern: mov #constant, dst (where dst will be checked by constraint)
    PATTERN = c_0

    # Replacement: Combine new high bits with existing low bits
    REPLACEMENT = (c_0 << 16) | (full_reg & 0xFFFF)

    # Constraint: Destination must be a high-half register (e.g., r6^2)
    CONSTRAINTS = [
        when.dst.is_high_half
    ]

    # Context: Bind 'full_reg' to the parent register (e.g., r6 from r6^2)
    CONTEXT_VARS = {
        "full_reg": context.dst.parent_register
    }

    # Side effect: Change destination from r6^2 to r6
    UPDATE_DESTINATION = "full_reg"

    # Skip verification: This rule changes the destination size
    SKIP_VERIFICATION = True
```

**Available helpers:**

**Context constraints (used in `CONSTRAINTS`):**

* `when.dst.is_high_half` - Check if destination is high-half register (e.g., r6^2)
* `when.dst.is_register` - Check if destination is a register
* `when.dst.is_memory` - Check if destination is a memory location

**Context providers (used in `CONTEXT_VARS`):**

* `context.dst.parent_register` - Get parent register (e.g., r6 from r6^2)
* `context.dst.operand_size` - Get destination size in bytes

**How it works:**

1. **Context inspection**: Constraints like `when.dst.is_high_half` check instruction properties
2. **Variable binding**: Providers like `context.dst.parent_register` bind values to variables
3. **Side effects**: `UPDATE_DESTINATION` modifies the instruction's destination operand
4. **No IDA imports**: Users write pure declarative logic; the framework handles IDA internals

**Why use context-aware DSL?**

* ✅ **Abstraction**: No need to understand IDA's C++ API (`mop_t`, `mop_r`, etc.)
* ✅ **Safety**: Framework handles dangerous mop creation and modification
* ✅ **Discoverability**: IDE autocomplete shows available helpers (`context.dst.*`, `when.dst.*`)
* ✅ **Testability**: Helpers are unit-testable in isolation
* ✅ **Maintainability**: Architecture-specific logic centralized in one place

For more examples, see `src/d810/optimizers/microcode/instructions/pattern_matching/rewrite_mov_context_aware.py`.

### Marking Known Failures

For rules that can't be verified with Z3:

```python
class MyUnverifiableRule(VerifiableRule):
    """This rule has size-dependent constraints."""

    SKIP_VERIFICATION = True  # Skip Z3 verification

    val_fe = Const("val_fe")

    PATTERN = ~(x ^ y) - (val_fe * (x | y))
    REPLACEMENT = (x + y) - 1

    CONSTRAINTS = [
        # Size-dependent constraint - can't auto-convert to Z3
        lambda ctx: (ctx['val_fe'].value + 2) & ((1 << (ctx['val_fe'].size * 8)) - 1) == 0
    ]
```

For mathematically incorrect rules:

```python
class MyKnownIncorrectRule(VerifiableRule):
    """This rule is only valid under very specific conditions."""

    KNOWN_INCORRECT = True  # Mark as incorrect

    PATTERN = ...
    REPLACEMENT = ...
```

### File Organization

Rules are organized in a dedicated package that is **independent of IDA**:

```bash
src/d810/mba/rules/
├── _base.py       # VerifiableRule base class and registry
├── __init__.py    # Package init - imports all rule modules
├── add.py         # Addition rules
├── and_.py        # Bitwise AND rules (underscore to avoid Python keyword)
├── bnot.py        # Bitwise NOT rules
├── cst.py         # Constant simplification rules
├── hodur.py       # Hodur deobfuscator patterns
├── misc.py        # Miscellaneous complex identities
├── mov.py         # Move/assignment rules
├── mul.py         # Multiplication rules
├── neg.py         # Negation rules
├── or_.py         # Bitwise OR rules (underscore to avoid Python keyword)
├── predicates.py  # Predicate/conditional rules
├── sub.py         # Subtraction rules
└── xor.py         # Bitwise XOR rules
```

**Architecture**: Pure symbolic rules live in `d810.mba.rules` (no IDA dependency). Context-aware rules that need IDA's microcode API stay in `d810.optimizers.microcode.instructions.pattern_matching/`.

Rules are automatically registered when imported. The `__init__.py` imports all modules:

```python
from d810.mba.rules import VerifiableRule

# All rules are now available via the registry
for name, rule_cls in VerifiableRule.registry.items():
    print(f"{name}: {rule_cls}")
```

### Unit Testing Without IDA (TDD Workflow)

**New!** Rules can now be developed and verified **without IDA Pro** using the pure DSL and Z3:

```bash
# Run all MBA unit tests (no IDA required!) - ~0.4 seconds
PYTHONPATH="src" python -m pytest tests/unit/mba/ -v

# Test specific rule verification
PYTHONPATH="src" python -m pytest tests/unit/mba/test_verifiable_rules.py -v
```

**TDD Workflow for New Rules:**

1. **Define your rule** in `tests/unit/mba/test_verifiable_rules.py` using pure DSL:

```python
from d810.mba.dsl import Var, Const, ONE, ZERO
from d810.mba.rules import VerifiableRule

x, y = Var("x"), Var("y")

class MyNewRule(VerifiableRule):
    """Simplify: (x | y) ^ (x & y) => x ^ y"""
    DESCRIPTION = "XOR identity using OR and AND"
    PATTERN = (x | y) ^ (x & y)
    REPLACEMENT = x ^ y
```

2. **Add to local registry** at the bottom of the test file:

```python
LOCAL_RULE_REGISTRY = [
    # ... existing rules ...
    MyNewRule,
]
```

3. **Run verification** (no IDA needed!):

```bash
PYTHONPATH="src" python -m pytest tests/unit/mba/test_verifiable_rules.py::test_rule_is_correct[MyNewRule] -v
```

4. **If verification passes**, copy your rule to the appropriate file in `src/d810/mba/rules/` (e.g., `xor.py`, `add.py`).

**Benefits of Unit Testing:**
- ⚡ **Fast feedback** - 49 rules verified in 0.4 seconds (vs ~12s with IDA)
- 🔓 **No license needed** - CI can run without IDA Pro
- 🧪 **True TDD** - Verify mathematical correctness before IDA integration
- 📦 **Isolated testing** - Test rules independently of IDA's microcode

### Automatic Verification (With IDA)

**Every rule is automatically verified with Z3!** The system test suite proves mathematical correctness:

```bash
# Test all 170 verified rules (requires IDA, takes ~12 seconds)
pytest tests/system/optimizers/test_verifiable_rules.py -v

# Test a specific rule
pytest tests/system/optimizers/test_verifiable_rules.py::test_rule_is_correct[MySimpleRule] -v
```

**How verification works:**

1. **Auto-registration**: Your rule class inherits from `VerifiableRule`, which automatically registers it
2. **Z3 conversion**: The DSL expressions are converted to Z3 bitvector formulas
3. **Constraint solving**: Z3 proves `PATTERN ⟺ REPLACEMENT` under all `CONSTRAINTS`
4. **Test generation**: A parameterized test is created for each rule automatically

**Verification coverage**: Currently **170/177 rules (96.0%)** are automatically verified. The remaining 7 rules are:

* 5 marked `KNOWN_INCORRECT` (kept for test parity with main branch)
* 2 marked `SKIP_VERIFICATION` (performance: complex MBA multiplication rules)

**What gets verified:**

* ✅ Algebraic identities (e.g., `(x | y) - (x & y) ⟺ x ^ y`)
* ✅ Constrained transformations (e.g., `(x ^ c1) + 2*(x & c2) ⟺ x + c1` when `c1 == c2`)
* ✅ Predicate simplifications (e.g., `(x | c1) != c2 ⟺ 1` when `(c1 | c2) != c2`)
* ✅ Dynamic constants (e.g., computing result constants from matched values)
* ✅ Extension operations (e.g., `Zext(x & 1, 32) == 2 ⟺ 0`)
* ✅ Bit-width-specific rules (e.g., byte operations with `BIT_WIDTH = 8`)

**Example test output:**

```bash
tests/unit/optimizers/test_verifiable_rules.py::TestVerifiableRules::test_rule_is_correct[Add_HackersDelightRule_1] PASSED
tests/unit/optimizers/test_verifiable_rules.py::TestVerifiableRules::test_rule_is_correct[Xor_Rule_1] PASSED
tests/unit/optimizers/test_verifiable_rules.py::TestVerifiableRules::test_rule_is_correct[PredSetnz_1] PASSED
tests/unit/optimizers/test_verifiable_rules.py::TestVerifiableRules::test_rule_is_correct[Xor_Hodur_2] PASSED
...
==================== 170 passed, 7 skipped in 12.44s ====================
```

**If a rule fails verification:**

```python
AssertionError: Z3 verification failed for MyBrokenRule:
Pattern:     (x | y) + (x & y)
Replacement: x * y
Counterexample: x = 1, y = 2
  Pattern evaluates to:     3
  Replacement evaluates to: 2
```

This immediate feedback prevents incorrect optimizations from being merged!

### Architecture: Pure Rules vs IDA-Specific Rules

D-810 ng separates **pure symbolic rules** from **IDA-specific integration code**:

```
d810.mba/                    # Pure symbolic (no IDA dependency)
├── dsl.py                   # Symbolic expression DSL
├── rules/                   # Pure rule definitions (177 rules)
│   ├── _base.py            # VerifiableRule base class
│   ├── xor.py, add.py, ... # Concrete rules
└── backends/
    ├── z3.py               # Z3 SMT verification
    └── ida.py              # IDA pattern adapter

d810.optimizers/             # IDA-specific code
├── extensions.py            # Context-aware DSL extensions
└── microcode/instructions/pattern_matching/
    └── experimental.py      # Rules requiring IDA context
```

**Key principle**: Rules in `d810.mba.rules` are **pure mathematics**. They define pattern/replacement pairs verified by Z3. The `d810.mba.backends.ida` module wraps these rules for IDA integration, providing:

- `IDAPatternAdapter`: Converts symbolic patterns to IDA AST matching
- `adapt_rules()`: Batch conversion of pure rules to IDA-compatible rules

**Context-Aware Extensions** (`d810.optimizers.extensions`):

Some rules need IDA-specific context (destination register type, operand size). These use the extension DSL:

```python
from d810.mba.dsl import Const, Var
from d810.mba.rules import VerifiableRule
from d810.optimizers.extensions import context, when

class FixHighMov(VerifiableRule):
    """Fix constant propagation for high-half registers."""

    PATTERN = c0
    REPLACEMENT = (full_reg & 0xFFFF) | (c0 << 16)

    # Check destination type (IDA-specific)
    CONSTRAINTS = [when.dst.is_high_half]

    # Bind variable from instruction context
    CONTEXT_VARS = {"full_reg": context.dst.parent_register}

    # Modify destination after replacement
    UPDATE_DESTINATION = "full_reg"
```

**Available context helpers:**

- `when.dst.is_high_half` - Destination is high-half register (e.g., r6^2)
- `when.dst.is_register` - Destination is any register
- `when.dst.is_memory` - Destination is memory location
- `context.dst.parent_register` - Get full 32-bit parent register
- `context.dst.operand_size` - Get destination size in bytes

**When to use context-aware rules:**

- Rules that check IDA-specific operand properties (register type, size)
- Rules that modify the destination operand (not just the source expression)
- Rules that need access to instruction metadata beyond the pattern

Context-aware rules stay in `d810.optimizers.microcode.instructions.pattern_matching/` since they depend on IDA APIs.

### Verification Engine Protocol

D-810 ng uses a **pluggable verification engine architecture** that decouples rules from the underlying solver (Z3, etc.):

```python
from d810.mba import VerificationOptions, VerificationEngine, Z3VerificationEngine

# Options dataclass for flexible configuration
opts = VerificationOptions(
    bit_width=32,      # Bitvector width (default 32)
    timeout_ms=5000,   # Solver timeout in milliseconds (0 = no timeout)
    verbose=False,     # Enable verbose output
    extra={}           # Engine-specific options
)

# Verify a rule with custom options
rule.verify(options=opts)

# Or use a specific engine
engine = Z3VerificationEngine()
rule.verify(engine=engine, options=opts)
```

**Protocol definition:**

```python
class VerificationEngine(Protocol):
    def create_variables(self, var_names: set[str], options: VerificationOptions) -> Dict[str, Any]:
        """Create solver-specific variables for symbolic names."""
        ...

    def prove_equivalence(
        self,
        pattern: SymbolicExpression,
        replacement: SymbolicExpression,
        variables: Dict[str, Any] | None = None,
        constraints: List[Any] | None = None,
        options: VerificationOptions = DEFAULT_OPTIONS,
    ) -> tuple[bool, Dict[str, int] | None]:
        """Prove pattern ⟺ replacement under constraints."""
        ...
```

**Benefits:**

* **Pluggable backends**: Z3 today, CVC5 or e-graphs tomorrow
* **Dependency injection**: Easy to mock for testing
* **Flexible options**: Timeout, bit-width, and engine-specific settings
* **Clean separation**: Rules don't import solver libraries directly

**Usage examples:**

```python
# Default: 32-bit, no timeout, Z3 backend
rule.verify()

# 64-bit verification
rule.verify(options=VerificationOptions(bit_width=64))

# With 5-second timeout
rule.verify(options=VerificationOptions(timeout_ms=5000))

# One-off transformation verification
from d810.mba import verify_transformation, Var

x, y = Var("x"), Var("y")
is_valid, counterexample = verify_transformation(
    pattern=(x | y) - (x & y),
    replacement=x ^ y,
    options=VerificationOptions(bit_width=32)
)
```

### DSL Reference

**Variables:**

* `Var("name")` - Symbolic variable (matches any expression)
* `x, y, z = Var("x_0"), Var("x_1"), Var("x_2")` - Pre-defined variables

**Constants:**

* `Const("name")` - Pattern-matching constant (symbolic)
* `Const("name", value)` - Concrete constant (e.g., `Const("ONE", 1)`)

**Operators:**

* Arithmetic: `+`, `-`, `*`
* Bitwise: `&`, `|`, `^`, `~`
* Shifts: `>>` (logical right), `.sar()` (arithmetic right), `<<` (left)

**Constraints:**

* Declarative: `c_1 == c_2`, `c_res == c_1 + c_2`
* Runtime: `lambda ctx: ctx["c_1"].value < 100`
* Helper: `when.is_bnot("x", "bnot_x")` - Check if one variable is bitwise NOT of another

### Best Practices

1. **Always add a docstring** explaining what the rule does
2. **Add meaningful DESCRIPTION and REFERENCE** fields
3. **Prefer declarative constraints** over lambdas (they auto-convert to Z3)
4. **Use clear variable names** (e.g., `c_mask` instead of `c_1`)
5. **Test edge cases** manually before relying on Z3
6. **Document why a rule is KNOWN_INCORRECT or SKIP_VERIFICATION**

## Examples

In `samples/src`, there are various `C` programs compiled using the `samples/src/Makefile` into a shared library, without optimizations (`-O0`). On Windows, that shared library is a `.dll`, on Darwin(Mac)/Linux, it is a `.so`. Included is an example compiled dll, `libobfuscated.dll`, that can serve as a testing ground for seeing the plugin in action. Please make a pull request with more obfuscation `C` examples to build a repository of obfuscated sample code for further research.

### How to build

The sample binaries are built via the `samples/Makefile`. You can cross-target OS and architecture.

* Default output name: `bins/<binary_name>_<hostos>_<arch>.<suffix>`
  * `<binary_name>` defaults to `libobfuscated` (override with `BINARY_NAME`)
  * `<hostos>` is the system you build on: `windows`, `darwin`, or `linux`
  * `<arch>` is the requested build arch (normalized): `x86_64`, `x86`, `arm64`, …
  * `<suffix>` comes from the target OS: `dll` (windows), `dylib` (darwin), `so` (linux)
* If you explicitly set `BINARY_NAME` (env or CLI), the output name is simplified to: `bins/<BINARY_NAME>.<suffix>`

Flags you can pass to `make`:

* `TARGET_OS` (default: `windows`)
  * One of: `windows`, `darwin`, `linux`, `native` (uses the host OS)
* `BUILD_ARCH` (default: `x86_64`)
  * Examples: `x86_64`, `x86`, `arm64`
  * Also accepts explicit compiler flags (e.g., `-m64`, `-m32`)
  * On macOS we use `-arch <name>` under the hood (e.g., `-arch x86_64`)
* `BINARY_NAME` (default: `libobfuscated`)

Notes:

* Builds are unoptimized by default: `-O0 -g` and inlining/vectorization are disabled.
* We rely on the host toolchain for linking. `TARGET_OS` selects the output suffix; cross-linking toolchains are up to your environment.

Examples (run from the repo root):

```bash
# Build defaults: Windows DLL for x86_64; name includes your host OS
cd samples && make
# → bins/libobfuscated_<hostos>_x86_64.dll

# Build Linux .so for arm64
make TARGET_OS=linux BUILD_ARCH=arm64
# → bins/libobfuscated_<hostos>_arm64.so

# Build macOS .dylib for x86_64
make TARGET_OS=darwin BUILD_ARCH=x86_64
# → bins/libobfuscated_<hostos>_x86_64.dylib

# Build for the native host OS, 32-bit x86
make TARGET_OS=native BUILD_ARCH=x86
# → bins/libobfuscated_<hostos>_x86.<ext>

# Customize the base name (explicit BINARY_NAME removes host/arch suffixes)
make BINARY_NAME=libobfuscatedv2
# → bins/libobfuscatedv2.<ext>

# Clean artifacts
make clean
```

### Contributing Samples

We welcome contributions of new obfuscated sample code! The repository includes an automated build system that makes it easy to contribute samples without requiring complex build setup.

#### How It Works

When you commit C source files to `samples/src/`, a GitHub Actions workflow automatically:

1. **Builds binaries** for all supported platforms and architectures:
   * **Windows**: x86_64, x86 (32-bit) → `.dll` files
   * **macOS**: x86_64 (Intel), arm64 (Apple Silicon) → `.dylib` files
   * **Linux**: x86_64, x86, arm64 → `.so` files

2. **Generates debug symbols**:
   * **Windows**: `.pdb` files (automatically generated by MSVC)
   * **macOS**: `.dSYM` bundles (generated via `dsymutil`)
   * **Linux**: Debug info embedded in `.so` files (compiled with `-g`)

3. **Commits results** back to the repository in `samples/bins/` with consistent naming:
   * `libobfuscated_windows_x86_64.dll` + `libobfuscated_windows_x86_64.pdb`
   * `libobfuscated_darwin_arm64.dylib` + `libobfuscated_darwin_arm64.dylib.dSYM/`
   * `libobfuscated_linux_x86_64.so` (with embedded debug symbols)

#### Adding a New Sample

To contribute a new obfuscated sample:

1. **Add your C source file** to `samples/src/c/`:

   ```bash
   # Example: Add a new virtualization obfuscation sample
   samples/src/c/my_new_obfuscation.c
   ```

2. **Commit and push**:

   ```bash
   git add samples/src/c/my_new_obfuscation.c
   git commit -m "feat: add virtualization obfuscation sample"
   git push
   ```

3. **Wait for automated build**: The GitHub Actions workflow will automatically:
   * Detect changes in `samples/src/`
   * Build binaries for all 7 platform/architecture combinations
   * Generate debug symbols
   * Commit built binaries to `samples/bins/`

4. **Use in tests**: Once the workflow completes, your sample binaries are ready to use in IDA Pro for testing deobfuscation rules.

#### Sample Guidelines

When contributing samples, please:

* **Add a descriptive comment** at the top of your C file explaining the obfuscation technique
* **Include meaningful function names** that describe what's being obfuscated
* **Document the source** if the obfuscation was generated by a tool (OLLVM, Tigress, etc.)
* **Keep samples focused**: Each file should demonstrate specific obfuscation techniques
* **Test locally first**: Verify your code compiles with the Makefile before committing

#### Example Sample Structure

```c
/**
 * Control Flow Flattening via State Machine
 *
 * Demonstrates a common obfuscation technique where control flow
 * is replaced with a state machine using a switch statement.
 *
 * Source: Hand-crafted example based on OLLVM control flow flattening
 */

#include <stdint.h>

int32_t flattened_function(int32_t input) {
    int32_t state = 0;
    int32_t result = 0;

    while (1) {
        switch (state) {
            case 0:
                result = input * 2;
                state = 1;
                break;
            case 1:
                result = result + 10;
                state = 2;
                break;
            case 2:
                return result;
        }
    }
}
```

#### Workflow Triggers

The build workflow is triggered automatically when:

* Files in `samples/src/` are modified
* The `samples/Makefile` is updated
* Header files in `samples/include/` change
* The workflow file itself is modified (`.github/workflows/build-binaries.yml`)

You can also manually trigger builds from the GitHub Actions tab using "Run workflow".

#### Build Artifacts

All built binaries and debug symbols are committed to the repository at `samples/bins/`:

```bash
samples/bins/
├── libobfuscated_windows_x86_64.dll
├── libobfuscated_windows_x86_64.pdb
├── libobfuscated_windows_x86.dll
├── libobfuscated_windows_x86.pdb
├── libobfuscated_darwin_x86_64.dylib
├── libobfuscated_darwin_x86_64.dylib.dSYM/
├── libobfuscated_darwin_arm64.dylib
├── libobfuscated_darwin_arm64.dylib.dSYM/
├── libobfuscated_linux_x86_64.so
├── libobfuscated_linux_x86.so
└── libobfuscated_linux_arm64.so
```

This ensures that anyone cloning the repository has immediate access to pre-built binaries for testing, regardless of their development environment.

### Test Constant Simplifications

**Before**: !["Before"](./docs/source/images/test_cst_simplification_before.png "Before Plugin")

**After**: !["After"](./docs/source/images/test_cst_simplification_after.png "After Plugin")

### Test XOR Simplifications

**Before**: !["Before"](./docs/source/images/test_xor_before.png "Before Plugin")

**After**: !["After"](./docs/source/images/test_xor_after.png "After Plugin")

## Vendored Dependencies

D810-ng employs vendoring dependencies ala [pip](https://github.com/pypa/pip/blob/main/src/pip/_vendor/README.rst) as well as uses its [Automatic Vendoring](https://github.com/pypa/pip/blob/main/src/pip/_vendor/README.rst#automatic-vendoring) via the [vendoring](https://pypi.org/project/vendoring/) tool. It is important to note that **vendoring is a development-time process, not a runtime dependency.**

* The `vendoring` tool is only needed by developers who add/update vendored packages
* End users do NOT need to install the `vendoring` tool
* Vendored packages are committed to git and distributed with d810
* At runtime, Python simply imports from `d810._vendor.*` like any other module

## Warnings

This plugin is still in early stage of development, so issues ~~may~~ will happen.

* Modifying incorrectly IDA microcode may lead IDA to crash. We try to detect that as much as possible to avoid crash, but since it may still happen **save you IDA database often**
* Plugin is tested on Windows, Mac and Linux.

## Documentation

Work in progress

Currently, you can read our [blog post](https://eshard.com/posts/) to get some information.

## Licenses

This library is licensed under LGPL V3 license. See the [LICENSE](LICENSE) file for details.

## Authors

See [AUTHORS](AUTHORS.md) for the list of contributors to the project.

## Acknowledgement

Rolf Rolles for the huge work he has done with his [HexRaysDeob plugin](https://github.com/RolfRolles/HexRaysDeob) and all the information about Hex-Rays microcode internals described in his [blog post](https://www.hex-rays.com/blog/hex-rays-microcode-api-vs-obfuscating-compiler/). We are still using some part of his plugin in D-810.

Dennis Elser for the [genmc plugin](https://github.com/patois/genmc) plugin which was very helpful for debugging D-810 errors.

A special thank you to [Boris Batteux](https://gitlab.com/borisbatteux) for this great plugin!
