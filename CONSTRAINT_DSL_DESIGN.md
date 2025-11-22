# Constraint DSL Design: Better Approach Than Lambda Parsing

## The Question

**"What's a better DSL way to add constraints than to parse lambdas?"**

## TL;DR

**Instead of parsing lambdas**, use **operator overloading** to build constraint expressions declaratively.

### Before (Lambda Parsing)
```python
val_res = DynamicConst("val_res", lambda ctx: ctx['c_2'].value - 1)
# Opaque lambda - must parse AST or extract from closure
```

### After (Declarative Constraints)
```python
val_res = Const("val_res")  # Symbolic constant
CONSTRAINTS = [val_res == c2 - ONE]  # Explicit, parseable constraint
```

---

## Why This Is Better

### 1. **Single Source of Truth**
The constraint `val_res == c2 - ONE` serves both purposes:
- **Z3 verification**: Adds symbolic constraint
- **Runtime matching**: Computes `val_res = c2.value - 1`

### 2. **No Parsing Required**
Python's operator overloading builds a data structure we can traverse:
```python
constraint = val_res == c2 - ONE
# Returns: EqualityConstraint(left=val_res, right=BinOp(c2, SUB, ONE))
# Not a lambda function object!
```

### 3. **Same DSL for Everything**
```python
PATTERN = (x ^ c1) + TWO * (x | c2)      # Uses DSL operators
REPLACEMENT = x + val_res                 # Uses DSL operators
CONSTRAINTS = [c1 == ~c2, val_res == c2 - ONE]  # Uses DSL operators!
```

Consistent syntax across all three components.

### 4. **Type-Checkable**
```python
# Type checker knows this returns ConstraintExpr
constraint: ConstraintExpr = val_res == c2 - ONE

# Lambda is opaque to type checkers
lambda ctx: ctx['c_2'].value - 1  # Type: Callable[[dict], int] - no semantic info
```

### 5. **Composable**
```python
CONSTRAINTS = [
    (c1 == ~c2) & (c3 == Const("ZERO", 0)),  # AND
    (val_res == c2 - ONE) | (val_res == c2 + ONE),  # OR
]
```

---

## Complete Example

### Original (Main Branch - No Verification)

```python
class Add_SpecialConstantRule_3(PatternMatchingRule):
    def check_candidate(self, candidate):
        # Runtime-only constraint checking
        if not equal_bnot_mop(candidate["c_1"].mop, candidate["c_2"].mop):
            return False

        # Runtime-only constant computation
        candidate.add_constant_leaf(
            "val_res", candidate["c_2"].value - 1, candidate["x_0"].size
        )
        return True

    @property
    def PATTERN(self) -> AstNode:
        return AstNode(m_add,
            AstNode(m_xor, AstLeaf("x_0"), AstConstant("c_1")),
            AstNode(m_mul, AstConstant("2", 2),
                AstNode(m_or, AstLeaf("x_0"), AstConstant("c_2"))))

    @property
    def REPLACEMENT_PATTERN(self) -> AstNode:
        return AstNode(m_add, AstLeaf("x_0"), AstConstant("val_res"))
```

**Problems:**
- No verification
- Imperative runtime code
- Pattern/replacement in verbose AST syntax
- Constraint logic hidden in check_candidate()

### Current Refactor (With Lambda Parsing)

```python
class Add_SpecialConstantRule_3(VerifiableRule):
    c1, c2 = Const("c_1"), Const("c_2")
    val_res = DynamicConst("val_res", lambda ctx: ctx['c_2'].value - 1, size_from="x")

    PATTERN = (x ^ c1) + TWO * (x | c2)
    REPLACEMENT = x + val_res

    CONSTRAINTS = [when.is_bnot("c_1", "c_2")]
```

**Problems:**
- Lambda is opaque: `lambda ctx: ctx['c_2'].value - 1`
- Must parse Python AST or extract from closure
- Runtime computation separated from verification formula
- when.is_bnot uses closure extraction (fragile)

### Proposed (Declarative Constraints)

```python
class Add_SpecialConstantRule_3(VerifiableRule):
    """Simplify: (x ^ c1) + 2*(x | c2) => x + val_res

    where:
        c1 == ~c2           (checking constraint)
        val_res == c2 - 1   (defining constraint)
    """

    c1, c2 = Const("c_1"), Const("c_2")
    val_res = Const("val_res")  # Symbolic constant (value defined by constraint)

    PATTERN = (x ^ c1) + TWO * (x | c2)
    REPLACEMENT = x + val_res

    CONSTRAINTS = [
        c1 == ~c2,          # Relationship between matched constants
        val_res == c2 - ONE  # Definition of replacement constant
    ]

    DESCRIPTION = "Simplify XOR-OR with inverted constants"
```

**Benefits:**
- ✅ Declarative constraints (no lambdas)
- ✅ Single source of truth for verification and runtime
- ✅ Type-checkable
- ✅ Composable (can add AND/OR)
- ✅ Clear separation: pattern matching vs. constraint checking

---

## Implementation Strategy

### Phase 1: Extend SymbolicExpression

Add comparison operators to SymbolicExpression:

```python
class SymbolicExpression:
    # ... existing operators: __add__, __sub__, etc.

    def __eq__(self, other) -> ConstraintExpr:
        """Equality constraint: self == other.

        NOTE: This returns a ConstraintExpr, not bool!
        Use `is` for object identity checks.
        """
        return EqualityConstraint(self, other)

    def __ne__(self, other) -> ConstraintExpr:
        return NotEqualConstraint(self, other)

    def __lt__(self, other) -> ConstraintExpr:
        return LessThanConstraint(self, other)

    # ... etc for >, <=, >=
```

### Phase 2: Constraint Expression Types

```python
@dataclass
class ConstraintExpr:
    """Base class for all constraints."""

    def to_z3(self, z3_vars: dict) -> z3.BoolRef:
        """Convert to Z3 constraint for verification."""
        raise NotImplementedError

    def check(self, candidate: dict) -> bool:
        """Check constraint with concrete runtime values."""
        raise NotImplementedError

    def define(self, candidate: dict) -> tuple[str, int] | None:
        """If this is a defining constraint, return (name, value)."""
        return None


@dataclass
class EqualityConstraint(ConstraintExpr):
    left: SymbolicExpression
    right: SymbolicExpression

    def to_z3(self, z3_vars: dict) -> z3.BoolRef:
        left_z3 = ast_to_z3_expression(self.left.node, z3_vars)
        right_z3 = ast_to_z3_expression(self.right.node, z3_vars)
        return left_z3 == right_z3

    def check(self, candidate: dict) -> bool:
        left_val = eval_expr(self.left, candidate)
        right_val = eval_expr(self.right, candidate)
        return left_val == right_val

    def define(self, candidate: dict) -> tuple[str, int] | None:
        # If left is a simple constant, define it as right's value
        if is_simple_constant(self.left):
            name = self.left.node.name
            value = eval_expr(self.right, candidate)
            return (name, value)
        return None
```

### Phase 3: Update VerifiableRule

```python
class VerifiableRule:
    def get_constraints(self, z3_vars: dict) -> list[z3.BoolRef]:
        """Convert CONSTRAINTS to Z3 expressions."""
        constraints = getattr(self, 'CONSTRAINTS', [])
        return [c.to_z3(z3_vars) for c in constraints if isinstance(c, ConstraintExpr)]

    def check_candidate(self, candidate: dict) -> bool:
        """Auto-generated from CONSTRAINTS."""
        constraints = getattr(self, 'CONSTRAINTS', [])

        for constraint in constraints:
            if isinstance(constraint, ConstraintExpr):
                # Try to define a constant
                definition = constraint.define(candidate)
                if definition:
                    name, value = definition
                    candidate.add_constant_leaf(name, value, ...)
                else:
                    # Check constraint
                    if not constraint.check(candidate):
                        return False
        return True
```

---

## Migration Path

### Step 1: Extend DSL (1 hour)
- Add `__eq__`, `__ne__` to SymbolicExpression
- Create ConstraintExpr classes

### Step 2: Update get_constraints() (30 min)
- Handle ConstraintExpr instances
- Keep legacy closure extraction for backward compatibility

### Step 3: Migrate Rules (4 hours)
Convert 49 DynamicConst rules:

**Before:**
```python
val_res = DynamicConst("val_res", lambda ctx: ctx['c_2'].value - 1)
```

**After:**
```python
val_res = Const("val_res")
CONSTRAINTS = [val_res == c2 - ONE]
```

### Step 4: Auto-generate check_candidate() (2 hours)
- Remove manual check_candidate() methods
- Generate from CONSTRAINTS

**Total: ~8 hours**

---

## Comparison Table

| Feature | Lambda Parsing | Declarative Constraints |
|---------|---------------|------------------------|
| **Readability** | ❌ Opaque | ✅ Clear |
| **Verification** | ⚠️ Must parse lambda | ✅ Direct conversion |
| **Runtime** | ✅ Direct execution | ✅ Auto-generated |
| **Type safety** | ❌ Callable[[dict], int] | ✅ ConstraintExpr |
| **Composability** | ❌ Can't combine lambdas | ✅ AND/OR operations |
| **Single source** | ❌ Duplicated logic | ✅ One constraint, dual use |
| **Debugging** | ❌ Stack traces in lambda | ✅ Constraint object inspection |
| **IDE support** | ❌ No autocomplete | ✅ Full autocomplete |

---

## Edge Cases

### Complex Constraints

**Scenario:** Constraint involves multiple operations

```python
# Lambda version (opaque)
lambda ctx: ((ctx['c_1'].value & 0xFF) == ctx['c_2'].value)

# Declarative version (clear)
(c1 & Const("mask", 0xFF)) == c2
```

### Multiple Definitions

**Scenario:** Multiple constants depend on same matched constant

```python
c1, c2 = Const("c_1"), Const("c_2")
val_a = Const("val_a")
val_b = Const("val_b")

CONSTRAINTS = [
    val_a == c1 + ONE,
    val_b == c2 - ONE,
]
```

### Conditional Constraints

**Scenario:** Constraint only applies in certain cases

```python
# Use OR composition
CONSTRAINTS = [
    (c1 == Const("ZERO", 0)) | (c2 == c1 * TWO),
]
```

---

## Recommendation

**✅ Use declarative constraints with operator overloading**

**Why:**
1. No lambda parsing complexity
2. Single source of truth for verification and runtime
3. Composable with standard boolean operators
4. Type-safe and IDE-friendly
5. Consistent with existing DSL design

**Implementation:**
- See `constraint_dsl_implementation.py` for working prototype
- Estimated effort: 8 hours to migrate all 49 DynamicConst rules
- Can be done incrementally (legacy lambda support maintained)

**Next step:**
Implement `__eq__` in SymbolicExpression and ConstraintExpr classes.
