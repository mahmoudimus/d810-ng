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
from d810.optimizers.rules import VerifiableRule
from d810.optimizers.dsl import Var, Const

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
- ✅ Automatically registered with d810
- ✅ Automatically tested with Z3 to prove correctness
- ✅ Ready to use in deobfuscation

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
from d810.optimizers.dsl import Var, Const, Zext

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
- Converts to Z3's `ZeroExt` for verification
- Maps to IDA's `M_XDU` opcode for pattern matching

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

Create your rules in the appropriate file under:
```
src/d810/optimizers/microcode/instructions/pattern_matching/
├── rewrite_add.py          # Addition/subtraction rules
├── rewrite_and.py          # Bitwise AND rules
├── rewrite_bnot.py         # Bitwise NOT rules
├── rewrite_cst.py          # Constant simplification rules
├── rewrite_misc.py         # Miscellaneous complex identities
├── rewrite_mov.py          # Move/assignment rules
├── rewrite_mul.py          # Multiplication rules
├── rewrite_neg.py          # Negation rules
├── rewrite_or.py           # Bitwise OR rules
├── rewrite_predicates.py   # Predicate/conditional rules
├── rewrite_sub.py          # Subtraction rules
└── rewrite_xor.py          # Bitwise XOR rules
```

Then import your module in `tests/unit/optimizers/test_verifiable_rules.py`:

```python
import d810.optimizers.microcode.instructions.pattern_matching.rewrite_add
```

### Automatic Verification

**Every rule is automatically verified with Z3!** The test suite proves mathematical correctness:

```bash
# Test all 167 verified rules (takes ~12 seconds)
pytest tests/unit/optimizers/test_verifiable_rules.py -v

# Test a specific rule
pytest tests/unit/optimizers/test_verifiable_rules.py::TestVerifiableRules::test_rule_is_correct[MySimpleRule] -v
```

**How verification works:**

1. **Auto-registration**: Your rule class inherits from `VerifiableRule`, which automatically registers it
2. **Z3 conversion**: The DSL expressions are converted to Z3 bitvector formulas
3. **Constraint solving**: Z3 proves `PATTERN ⟺ REPLACEMENT` under all `CONSTRAINTS`
4. **Test generation**: A parameterized test is created for each rule automatically

**Verification coverage**: Currently **167/174 rules (95.9%)** are automatically verified. The remaining 7 rules are:
- 5 marked `KNOWN_INCORRECT` (kept for test parity with main branch)
- 2 marked `SKIP_VERIFICATION` (performance: complex MBA multiplication rules)

**What gets verified:**

- ✅ Algebraic identities (e.g., `(x | y) - (x & y) ⟺ x ^ y`)
- ✅ Constrained transformations (e.g., `(x ^ c1) + 2*(x & c2) ⟺ x + c1` when `c1 == c2`)
- ✅ Predicate simplifications (e.g., `(x | c1) != c2 ⟺ 1` when `(c1 | c2) != c2`)
- ✅ Dynamic constants (e.g., computing result constants from matched values)
- ✅ Extension operations (e.g., `Zext(x & 1, 32) == 2 ⟺ 0`)

**Example test output:**

```
tests/unit/optimizers/test_verifiable_rules.py::TestVerifiableRules::test_rule_is_correct[Add_HackersDelightRule_1] PASSED
tests/unit/optimizers/test_verifiable_rules.py::TestVerifiableRules::test_rule_is_correct[Xor_Rule_1] PASSED
tests/unit/optimizers/test_verifiable_rules.py::TestVerifiableRules::test_rule_is_correct[PredSetnz_1] PASSED
...
==================== 167 passed, 7 skipped in 12.67s ====================
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

### DSL Reference

**Variables:**
- `Var("name")` - Symbolic variable (matches any expression)
- `x, y, z = Var("x_0"), Var("x_1"), Var("x_2")` - Pre-defined variables

**Constants:**
- `Const("name")` - Pattern-matching constant (symbolic)
- `Const("name", value)` - Concrete constant (e.g., `Const("ONE", 1)`)

**Operators:**
- Arithmetic: `+`, `-`, `*`
- Bitwise: `&`, `|`, `^`, `~`
- Shifts: `>>` (logical right), `.sar()` (arithmetic right), `<<` (left)

**Constraints:**
- Declarative: `c_1 == c_2`, `c_res == c_1 + c_2`
- Runtime: `lambda ctx: ctx["c_1"].value < 100`
- Helper: `when.is_bnot("x", "bnot_x")` - Check if one variable is bitwise NOT of another

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

### Test Constant Simplifications

**Before**: !["Before"](./docs/source/images/test_cst_simplification_before.png "Before Plugin")

**After**: !["After"](./docs/source/images/test_cst_simplification_after.png "After Plugin")

### Test XOR Simplifications

**Before**: !["Before"](./docs/source/images/test_xor_before.png "Before Plugin")

**After**: !["After"](./docs/source/images/test_xor_after.png "After Plugin")

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
# CI/CD with IDA Pro
