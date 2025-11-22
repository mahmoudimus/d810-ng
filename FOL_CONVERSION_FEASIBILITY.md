# FOL DSL Conversion Feasibility Assessment

## Executive Summary

**Total Rules:** 162
**Estimated Conversion Effort:** 2-3 weeks (with tooling)
**Recommendation:** ✅ **FEASIBLE** - Proceed with phased approach

---

## Rule Breakdown by Complexity

### Category 1: Simple Rules (74 rules, 45.7%)
**No constraints, no dynamic constants**

**Conversion Effort:** ~30 seconds per rule (automated)

**Example Before:**
```python
class Add_HackersDelightRule_1(VerifiableRule):
    PATTERN = x - (~y + ONE)
    REPLACEMENT = x + y
    DESCRIPTION = "Simplify subtraction of two's complement to addition"
```

**Example After:**
```python
Add_HackersDelightRule_1 = RuleSpec(
    name="Add_HackersDelightRule_1",
    description="Simplify subtraction of two's complement to addition",

    correctness=Forall(
        vars=[x, y],
        body=BvEq(
            left=BvExpr(BvOp.SUB, [x, BvExpr(BvOp.ADD, [BvExpr(BvOp.NOT, [y]), ONE])]),
            right=BvExpr(BvOp.ADD, [x, y])
        )
    ),

    pattern=BvExpr(BvOp.SUB, [x, BvExpr(BvOp.ADD, [BvExpr(BvOp.NOT, [y]), ONE])]),
    replacement=BvExpr(BvOp.ADD, [x, y])
)
```

**Or with builder pattern:**
```python
Add_HackersDelightRule_1 = (
    Rule("Add_HackersDelightRule_1")
    .forall(x, y)
    .proves((x - (~y + ONE)) == (x + y))
    .pattern(x - (~y + ONE))
    .replacement(x + y)
)
```

---

### Category 2: Constrained Rules (39 rules, 24.1%)
**Has CONSTRAINTS but no DynamicConst**

**Conversion Effort:** ~2 minutes per rule (semi-automated)

**Example Before:**
```python
class Add_SpecialConstantRule_1(VerifiableRule):
    PATTERN = (x ^ Const("c_1")) + TWO * (x & Const("c_2"))
    REPLACEMENT = x + Const("c_1")
    CONSTRAINTS = [when.equal_mops("c_1", "c_2")]
```

**Example After:**
```python
Add_SpecialConstantRule_1 = RuleSpec(
    name="Add_SpecialConstantRule_1",
    description="Simplify XOR-AND with equal constants",

    correctness=Forall(
        vars=[x, c1],  # c2 is eliminated by constraint
        body=BvEq(
            left=(x ^ c1) + TWO * (x & c1),
            right=x + c1
        )
    ),

    pattern=(x ^ c1) + TWO * (x & c2),
    replacement=x + c1,
    constraints=[BvEq(c1, c2)]
)
```

**Constraint type distribution:**
- `is_bnot(c1, c2)` [c1 == ~c2]: 49 instances
- Lambda functions: 31 instances
- `equal_mops(c1, c2)` [c1 == c2]: 1 instance

---

### Category 3: Dynamic Constants Only (27 rules, 16.7%)
**Has DynamicConst but no constraints**

**Conversion Effort:** ~3 minutes per rule (manual)

**Challenge:** DynamicConst is runtime-only (pattern matching), not verifiable

**Example Before:**
```python
class Add_OllvmRule_DynamicConst(VerifiableRule):
    val_1 = DynamicConst("val_1", lambda ctx: 1, size_from="x")
    PATTERN = ~(x ^ y) + TWO * (y | x)
    REPLACEMENT = (x + y) - val_1
```

**Example After (option 1 - inline constant):**
```python
# For verification: substitute known value
Add_OllvmRule_DynamicConst = RuleSpec(
    correctness=Forall(
        vars=[x, y],
        body=BvEq(
            ~(x ^ y) + TWO * (y | x),
            (x + y) - ONE  # val_1 is always 1
        )
    ),
    pattern=~(x ^ y) + TWO * (y | x),
    replacement=(x + y) - DynamicConst("val_1", lambda ctx: 1)
)
```

**Example After (option 2 - separate verification):**
```python
# Verify the mathematical identity separately
Add_OllvmRule_DynamicConst_Correctness = Forall([x, y],
    (~(x ^ y) + TWO * (y | x)) == ((x + y) - ONE))

# Pattern matching spec (runtime only)
Add_OllvmRule_DynamicConst_Pattern = PatternSpec(
    pattern=~(x ^ y) + TWO * (y | x),
    replacement=lambda ctx: (x + y) - ctx.mk_const(1)
)
```

---

### Category 4: Both Constraints + Dynamic (22 rules, 13.6%)
**Most complex - has both CONSTRAINTS and DynamicConst**

**Conversion Effort:** ~5 minutes per rule (manual)

**Example Before:**
```python
class Add_SpecialConstantRule_3(VerifiableRule):
    c1, c2 = Const("c_1"), Const("c_2")
    val_res = DynamicConst("val_res", lambda ctx: ctx['c_2'].value - 1, size_from="x")

    PATTERN = (x ^ c1) + TWO * (x | c2)
    REPLACEMENT = x + val_res
    CONSTRAINTS = [when.is_bnot("c_1", "c_2")]
```

**Example After:**
```python
Add_SpecialConstantRule_3 = RuleSpec(
    name="Add_SpecialConstantRule_3",
    description="Simplify XOR-OR with inverted constants",

    # For verification: express val_res in terms of c2
    correctness=Forall(
        vars=[x, c2],
        body=BvEq(
            (x ^ ~c2) + TWO * (x | c2),  # c1 = ~c2 by constraint
            x + (c2 - ONE)                # val_res = c2 - 1
        )
    ),

    # For runtime pattern matching
    pattern=(x ^ c1) + TWO * (x | c2),
    replacement=x + DynamicConst("val_res", lambda ctx: ctx['c_2'].value - 1),
    constraints=[BvEq(c1, BvExpr(BvOp.NOT, [c2]))]
)
```

---

## Operations Coverage

**Operations used in all 162 rules:** 10 total

✅ All covered by proposed FOL DSL:
- NEG (unary minus)
- BNOT (bitwise not ~)
- ADD (+)
- SUB (-)
- MUL (*)
- OR (|)
- AND (&)
- XOR (^)
- LSHR (logical shift right >>)
- ASHR (arithmetic shift right)

**No exotic operations needed** (no division, modulo, comparisons in current rules)

---

## Constraint Predicates Needed

Based on 81 constraint instances:

1. **BvEq** - bitwise equality (c1 == c2) - **1 use**
2. **BvNot** - bitwise not constraint (c1 == ~c2) - **49 uses**
3. **Lambda predicates** - custom constraints - **31 uses**

**Most common lambda patterns:**
```python
# Pattern 1: Bit mask check (16 instances)
lambda ctx: (ctx['c_1'].value & 0xFF) == ctx['c_2'].value

# Pattern 2: Size-dependent wrapping (10 instances)
lambda ctx: (ctx['val_fe'].value + 2) & ((1 << (ctx['val_fe'].size * 8)) - 1) == 0

# Pattern 3: Misc arithmetic (5 instances)
lambda ctx: ctx['c_1'].value == ctx['c_2'].value + ctx['c_3'].value
```

**Can be expressed as:**
```python
# FOL encoding
And([
    BvEq(BvExpr(BvOp.AND, [c1, Const("mask", 0xFF)]), c2)
])
```

---

## Conversion Strategy

### Phase 1: Tooling (Week 1)
Build conversion automation:

```python
def convert_simple_rule(rule_class):
    """Auto-convert Category 1 rules."""
    # Extract AST pattern/replacement
    # Generate Forall formula
    # Generate RuleSpec

def convert_constrained_rule(rule_class):
    """Semi-auto convert Category 2 rules."""
    # Parse constraints
    # Simplify formula by eliminating constrained variables
    # Generate RuleSpec

def convert_dynamic_rule(rule_class):
    """Manual template for Category 3/4."""
    # Human reviews DynamicConst computation
    # Inline or separate verification
```

### Phase 2: Batch Conversion (Week 2)
- Day 1-2: Convert 74 simple rules (automated)
- Day 3-4: Convert 39 constrained rules (semi-automated)
- Day 5: Convert 27 dynamic rules (manual with templates)

### Phase 3: Complex Rules (Week 3)
- Day 1-2: Convert 22 constrained+dynamic rules (manual)
- Day 3-4: Verification and testing
- Day 5: Documentation and cleanup

---

## Risk Assessment

### Low Risk
✅ Simple rules (45.7%) - fully automatable
✅ Operations coverage - all 10 ops already handled
✅ Most constraints are simple (BvEq, BvNot)

### Medium Risk
⚠️ Lambda constraints (31 instances) - need manual translation to FOL
⚠️ DynamicConst verification - requires separate treatment

### High Risk
❌ None identified

---

## Effort Estimates

| Category | Rules | Time/Rule | Total Time | Automation |
|----------|-------|-----------|------------|------------|
| Simple   | 74    | 30 sec    | 37 min     | 100%       |
| Constrained | 39 | 2 min     | 78 min     | 80%        |
| Dynamic  | 27    | 3 min     | 81 min     | 40%        |
| Both     | 22    | 5 min     | 110 min    | 30%        |
| **Total** | **162** | **~2 min avg** | **~5 hours** | **65%** |

**Plus tooling development:** 2-3 days
**Plus testing/verification:** 3-5 days
**Plus documentation:** 1-2 days

**Total calendar time:** 2-3 weeks with one developer

---

## Example Conversion Pipeline

```python
# Step 1: Parse existing rule
rule_cls = Add_HackersDelightRule_1

# Step 2: Extract components
pattern_ast = rule_cls.PATTERN.node
replacement_ast = rule_cls.REPLACEMENT.node
constraints = getattr(rule_cls, 'CONSTRAINTS', [])

# Step 3: Convert to FOL
pattern_fol = ast_to_fol(pattern_ast)
replacement_fol = ast_to_fol(replacement_ast)

# Step 4: Build spec
vars = extract_vars(pattern_fol, replacement_fol)
spec = RuleSpec(
    name=rule_cls.__name__,
    description=rule_cls.DESCRIPTION,
    correctness=Forall(vars, BvEq(pattern_fol, replacement_fol)),
    pattern=pattern_fol,
    replacement=replacement_fol
)

# Step 5: Verify
verify(spec)  # Uses Z3 backend
```

---

## Recommendation

**✅ PROCEED** with FOL DSL conversion

**Why:**
1. **High automation potential** (65% of work can be scripted)
2. **Clean separation** between verification and pattern matching
3. **No blockers** - all operations and constraints are expressible
4. **Incremental path** - can convert module-by-module
5. **Long-term payoff** - better verification, multiple backends, clearer semantics

**Start with:**
- Implement FOL DSL core (2-3 days)
- Build conversion tooling (2-3 days)
- Convert `rewrite_add_refactored.py` as proof-of-concept (1 day)
- Measure actual vs estimated effort
- Scale to remaining modules

**Quick win:** Even partial conversion (just Category 1 rules) gives immediate value
