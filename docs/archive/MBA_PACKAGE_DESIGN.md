# MBA Package Design: Separating Z3 Verification Logic

> **ARCHIVED**: This design document has been **implemented** as of 2025-11-25.
> The `d810.mba` package now exists with:
> - `mba/dsl.py` - Symbolic expression DSL
> - `mba/rules/` - Pure rule definitions (177 rules)
> - `mba/backends/z3.py` - Z3 SMT verification
> - `mba/backends/ida.py` - IDA pattern adapter
>
> See the main [README.md](../../README.md#architecture-pure-rules-vs-ida-specific-rules) for current architecture.

## Overview

This document proposes restructuring the Z3-based verification and MBA (Mixed Boolean Arithmetic) simplification logic into a standalone package: `d810.mba`.

**Goals**:
1. **Separation of Concerns**: Decouple MBA/Z3 logic from IDA-specific optimizers
2. **Reusability**: Make the DSL and verification framework usable outside d810
3. **Clarity**: Clear boundaries between symbolic expressions, Z3 proving, and IDA integration
4. **Testability**: Test MBA logic without IDA Pro dependencies
5. **Future-proofing**: Enable other projects to use the MBA verification framework

## Current Structure (Problems)

```
src/d810/
├── expr/
│   ├── z3_utils.py              (574 LOC) - Z3 proving utilities
│   ├── visitors.py              (474 LOC) - AST to Z3 conversion
│   └── ast.py                              - IDA-specific AST
│
└── optimizers/
    ├── dsl.py                   (696 LOC) - Symbolic expression DSL
    ├── constraints.py           (608 LOC) - Constraint expressions
    ├── rules.py                 (657 LOC) - VerifiableRule (mixes IDA + Z3)
    └── microcode/instructions/pattern_matching/
        └── rewrite_*.py         (4500+ LOC) - 177 concrete rules
```

**Problems**:
1. `dsl.py` is in `optimizers/` but should be a core abstraction
2. `z3_utils.py` is in `expr/` (IDA-specific) but could be standalone
3. `VerifiableRule` in `rules.py` mixes:
   - Pattern matching (IDA-specific)
   - Z3 verification (generic)
   - Symbolic DSL (generic)
4. Hard to test MBA logic without IDA Pro
5. Can't reuse the verification framework for non-IDA projects

## Proposed Structure

```
src/d810/
├── mba/                         # NEW: Standalone MBA package
│   ├── __init__.py
│   ├── dsl.py                   # Symbolic expression DSL (moved from optimizers/)
│   ├── constraints.py           # Constraint system (moved from optimizers/)
│   ├── z3_backend.py            # Z3 proving engine (moved from expr/z3_utils.py)
│   ├── visitors.py              # Expression visitors (moved from expr/visitors.py)
│   ├── verifier.py              # NEW: Pure verification logic (extracted from rules.py)
│   ├── simplifier.py            # NEW: MBA simplification algorithms
│   └── types.py                 # NEW: Type definitions for MBA expressions
│
├── expr/                        # IDA-specific expression handling
│   ├── ast.py                   # IDA microcode AST
│   ├── emulator.py              # Microcode emulation
│   └── utils.py                 # AST utilities
│
└── optimizers/
    ├── core.py                  # Optimization protocols
    ├── rules.py                 # NEW: PatternRule (IDA-specific, uses mba.verifier)
    └── microcode/instructions/pattern_matching/
        └── rewrite_*.py         # 177 concrete rules (import from d810.mba)
```

## Package Breakdown

### 1. `d810.mba.dsl` (Symbolic Expressions)

**Purpose**: Define symbolic variables and expressions with operator overloading.

**Contents** (from current `optimizers/dsl.py`):
- `SymbolicExpression` - Base class with operator overloading
- `Var(name)` - Factory for symbolic variables
- `Const(name, value)` - Factory for constants
- `Zext(expr, width)` - Zero-extension
- Operator overloads: `+`, `-`, `*`, `&`, `|`, `^`, `~`, `<<`, `>>`

**Dependencies**: None (pure Python)

**Example**:
```python
from d810.mba.dsl import Var, Const

x, y = Var("x"), Var("y")
c1 = Const("c1", 42)

# Build symbolic expressions
expr1 = (x | y) - (x & y)  # x XOR y identity
expr2 = x ^ y

# No IDA dependencies!
```

### 2. `d810.mba.constraints` (Constraint System)

**Purpose**: Define boolean constraints on symbolic expressions.

**Contents** (from current `optimizers/constraints.py`):
- `ConstraintExpr` - Boolean constraint expressions
- `Comparison` operators: `==`, `!=`, `<`, `<=`, `>`, `>=`
- `LogicalOps`: `&` (and), `|` (or), `~` (not)
- `.to_int()` - Convert boolean to 0/1 integer

**Dependencies**: `d810.mba.dsl`

**Example**:
```python
from d810.mba.dsl import Var, Const
from d810.mba.constraints import Constraint

x, c1, c2 = Var("x"), Const("c1"), Const("c2")

# Define constraints
constraint1 = c2 == ~c1  # c2 must be bitwise NOT of c1
constraint2 = (c1 < c2) & (c1 != 0)  # c1 less than c2 AND non-zero

# Use in verification
```

### 3. `d810.mba.z3_backend` (Z3 Proving Engine)

**Purpose**: Interface to Z3 theorem prover for equivalence checking.

**Contents** (from current `expr/z3_utils.py`):
- `prove_equivalence(expr1, expr2, constraints, bit_width)` - Main API
- `get_counterexample(expr1, expr2)` - Find violations
- Helper functions for Z3 solver configuration

**Dependencies**:
- `z3-solver` (external)
- `d810.mba.dsl`
- `d810.mba.constraints`

**Example**:
```python
from d810.mba.dsl import Var
from d810.mba.z3_backend import prove_equivalence

x, y = Var("x"), Var("y")

# Prove XOR identity
pattern = (x | y) - (x & y)
replacement = x ^ y

is_equiv, counterexample = prove_equivalence(
    pattern,
    replacement,
    constraints=[],
    bit_width=32
)

assert is_equiv  # Proven correct!
```

### 4. `d810.mba.visitors` (Expression Visitors)

**Purpose**: Convert symbolic expressions to different representations.

**Contents** (from current `expr/visitors.py`):
- `Z3Visitor` - Convert `SymbolicExpression` → Z3 bitvector
- `AstVisitor` - Convert `SymbolicExpression` → IDA `AstNode` (NEW location)
- `StringVisitor` - Convert to human-readable string
- `SimplifyVisitor` - Apply algebraic simplifications

**Dependencies**:
- `d810.mba.dsl`
- `d810.mba.constraints`
- `z3-solver` (for Z3Visitor)
- `d810.expr.ast` (for AstVisitor - optional)

**Example**:
```python
from d810.mba.dsl import Var
from d810.mba.visitors import Z3Visitor, StringVisitor

x = Var("x")
expr = ~x + Const("1", 1)

# Convert to Z3
z3_visitor = Z3Visitor(bit_width=32)
z3_expr = expr.accept(z3_visitor)

# Convert to string
str_visitor = StringVisitor()
print(expr.accept(str_visitor))  # "~x + 1"
```

### 5. `d810.mba.verifier` (Verification Engine)

**Purpose**: Core verification logic extracted from `VerifiableRule`.

**Contents** (NEW - extracted from `optimizers/rules.py`):
- `MBARule` - Abstract base for MBA transformation rules
- `verify_transformation(pattern, replacement, constraints, bit_width)` - Pure function
- `RuleVerifier` - Class for batch verification

**Dependencies**:
- `d810.mba.dsl`
- `d810.mba.constraints`
- `d810.mba.z3_backend`

**Key Difference**: This is **IDA-agnostic**. No `minsn_t`, no `AstNode`, just symbolic math.

**Example**:
```python
from d810.mba.verifier import MBARule, verify_transformation
from d810.mba.dsl import Var

class XorIdentity(MBARule):
    """(x | y) - (x & y) ≡ x ^ y"""
    name = "XorFromOrAndSub"

    def __init__(self):
        x, y = Var("x"), Var("y")
        self.pattern = (x | y) - (x & y)
        self.replacement = x ^ y

    def verify(self):
        return verify_transformation(
            self.pattern,
            self.replacement,
            constraints=[],
            bit_width=32
        )

# Verify correctness
rule = XorIdentity()
assert rule.verify()  # No IDA needed!
```

### 6. `d810.mba.simplifier` (MBA Simplification)

**Purpose**: Algorithms for simplifying MBA expressions.

**Contents** (NEW):
- `simplify(expr)` - Apply algebraic simplifications
- `normalize(expr)` - Canonical form
- `complexity_score(expr)` - Heuristic for expression complexity
- MBA obfuscation detection heuristics

**Dependencies**: `d810.mba.dsl`

**Example**:
```python
from d810.mba.dsl import Var, Const
from d810.mba.simplifier import simplify

x = Var("x")

# Complex MBA-obfuscated expression
obfuscated = (x ^ 0xFF) + 1  # Really just -x for 8-bit

simplified = simplify(obfuscated, bit_width=8)
# Result: -x
```

### 7. `d810.mba.types` (Type Definitions)

**Purpose**: Type hints and protocols for the MBA package.

**Contents** (NEW):
- `Expression` - Type alias for symbolic expressions
- `Constraint` - Type alias for constraints
- `BitWidth` - Literal type for bit widths (8, 16, 32, 64)
- `VerificationResult` - Result tuple (is_equivalent, counterexample)

**Dependencies**: `typing` module only

## Integration with IDA-Specific Code

After the restructuring, IDA-specific code imports from `d810.mba`:

### Updated `d810.optimizers.rules.py`

```python
"""IDA-specific optimization rules using MBA verification."""

from __future__ import annotations
import abc
from typing import List, Dict, Any

from ida_hexrays import minsn_t
from d810.expr.ast import AstNode, minsn_to_ast
from d810.optimizers.core import OptimizationContext

# Import from MBA package
from d810.mba.dsl import SymbolicExpression
from d810.mba.constraints import ConstraintExpr
from d810.mba.verifier import MBARule, verify_transformation
from d810.mba.visitors import AstVisitor

class VerifiablePatternRule(abc.ABC):
    """IDA pattern rule with MBA verification.

    This bridges the gap between:
    - d810.mba (generic MBA verification)
    - IDA Pro (microcode pattern matching)
    """

    # Symbolic definitions (from d810.mba)
    @property
    @abc.abstractmethod
    def PATTERN(self) -> SymbolicExpression: ...

    @property
    @abc.abstractmethod
    def REPLACEMENT(self) -> SymbolicExpression: ...

    CONSTRAINTS: List[ConstraintExpr] = []
    BIT_WIDTH: int = 32

    def verify(self) -> bool:
        """Verify using MBA verification engine."""
        return verify_transformation(
            self.PATTERN,
            self.REPLACEMENT,
            self.CONSTRAINTS,
            self.BIT_WIDTH
        )

    def apply(self, context: OptimizationContext, ins: minsn_t) -> int:
        """Apply pattern matching (IDA-specific)."""
        # Convert symbolic expressions to IDA AstNodes
        ast_visitor = AstVisitor()
        pattern_ast = self.PATTERN.accept(ast_visitor)

        # IDA-specific matching logic
        current_ast = minsn_to_ast(ins)
        if pattern_ast.matches(current_ast):
            replacement_ast = self.REPLACEMENT.accept(ast_visitor)
            # ... replace instruction ...
            return 1
        return 0
```

### Updated Rule Definitions

```python
# d810/optimizers/microcode/instructions/pattern_matching/rewrite_xor.py

from d810.mba.dsl import Var
from d810.optimizers.rules import VerifiablePatternRule

x, y = Var("x"), Var("y")

class XorFromOrAndSub(VerifiablePatternRule):
    """(x | y) - (x & y) ≡ x ^ y"""
    NAME = "XorFromOrAndSub"
    DESCRIPTION = "Recognize XOR from OR-AND-SUB pattern"

    PATTERN = (x | y) - (x & y)
    REPLACEMENT = x ^ y

# Verification happens automatically via VerifiablePatternRule.verify()
```

## Migration Path

### Phase 1: Create Package Structure
1. Create `src/d810/mba/` directory
2. Create `__init__.py` with exports
3. Don't move files yet, just set up structure

### Phase 2: Move Pure Logic (No Breaking Changes)
1. **Copy** (don't move) `dsl.py` to `mba/dsl.py`
2. **Copy** `constraints.py` to `mba/constraints.py`
3. **Copy** `z3_utils.py` to `mba/z3_backend.py`
4. **Copy** relevant parts of `visitors.py` to `mba/visitors.py`
5. Keep originals, add deprecation warnings

### Phase 3: Extract Verifier
1. Extract pure verification logic from `rules.py::VerifiableRule`
2. Create `mba/verifier.py` with `MBARule` and `verify_transformation()`
3. Update `VerifiableRule` to use `mba.verifier` internally
4. No breaking changes to rule definitions yet

### Phase 4: Update Imports (Breaking Changes)
1. Update all `rewrite_*.py` files to import from `d810.mba.dsl`
2. Update `rules.py` to import from `d810.mba.verifier`
3. Update documentation
4. Run full test suite

### Phase 5: Clean Up
1. Remove original files from `optimizers/` and `expr/`
2. Remove deprecation warnings
3. Update `setup.py` to include `d810.mba` as a package

## Benefits

### 1. Clear Separation
```
d810.mba          → Generic MBA verification (no IDA dependency)
d810.expr         → IDA-specific AST and emulation
d810.optimizers   → IDA-specific optimizations (uses d810.mba)
```

### 2. Reusability
Other projects can use `d810.mba` for:
- MBA expression simplification
- Symbolic execution
- Program synthesis
- Theorem proving for bitvector expressions

### 3. Testing
```python
# Can test MBA logic without IDA Pro!
import pytest
from d810.mba.dsl import Var
from d810.mba.verifier import verify_transformation

def test_xor_identity():
    x, y = Var("x"), Var("y")
    assert verify_transformation((x | y) - (x & y), x ^ y)

# No need for: ida_hexrays, mba_t, minsn_t, etc.
```

### 4. Documentation
Easier to document MBA verification independently:
```
docs/
├── mba/
│   ├── tutorial.md       # Using the MBA DSL
│   ├── verification.md   # Z3-based verification
│   └── api.md            # API reference
└── optimizers/
    └── writing_rules.md  # IDA-specific rule writing
```

### 5. Future Extensions
- MBA obfuscation toolkit (inverse of simplification)
- Integration with other SMT solvers (CVC5, Bitwuzla)
- Expression database for known identities
- Machine learning for MBA pattern recognition

## Package Dependencies

```
d810.mba:
  - z3-solver (external)
  - typing (stdlib)
  - dataclasses (stdlib)

d810.expr:
  - ida_hexrays (IDA SDK)
  - d810.mba (for AST visitor)

d810.optimizers:
  - ida_hexrays (IDA SDK)
  - d810.mba (for DSL and verification)
  - d810.expr (for AST)
```

## Example: Standalone MBA Verification Script

```python
#!/usr/bin/env python3
"""Verify MBA transformation rules without IDA Pro."""

from d810.mba.dsl import Var, Const
from d810.mba.constraints import Constraint
from d810.mba.verifier import MBARule, RuleVerifier

# Define rules using only d810.mba
x, y, c = Var("x"), Var("y"), Const("c")

class XorIdentity1(MBARule):
    name = "XOR from OR-AND-SUB"
    pattern = (x | y) - (x & y)
    replacement = x ^ y

class XorIdentity2(MBARule):
    name = "XOR from XOR-AND-shift"
    pattern = ((x ^ y) + 2 * (x & y))
    replacement = x | y

class NegIdentity(MBARule):
    name = "NEG from NOT-ADD"
    pattern = ~x + Const("1", 1)
    replacement = -x

# Batch verification
verifier = RuleVerifier()
verifier.add_rules([XorIdentity1(), XorIdentity2(), NegIdentity()])

results = verifier.verify_all()
for rule_name, is_valid in results.items():
    status = "✓" if is_valid else "✗"
    print(f"{status} {rule_name}")

# Output:
# ✓ XOR from OR-AND-SUB
# ✓ XOR from XOR-AND-shift
# ✓ NEG from NOT-ADD
```

No IDA Pro needed! This script can run on any machine with Python + Z3.

## Conclusion

Restructuring into `d810.mba` provides:
- **Modularity**: Clear package boundaries
- **Testability**: Test MBA logic without IDA
- **Reusability**: Other projects can use the MBA framework
- **Maintainability**: Easier to understand and modify
- **Extensibility**: Foundation for future MBA research

The migration can be done incrementally without breaking existing code, making it low-risk.

**Estimated effort**: 12-16 hours
- Phase 1-2: 2-3 hours (copying files)
- Phase 3: 4-6 hours (extracting verifier)
- Phase 4: 4-5 hours (updating imports)
- Phase 5: 2 hours (cleanup)
