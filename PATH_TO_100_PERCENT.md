# Path to 100%: Test Pass Rate & Automation

## Current Status

**Test Results:** ~40-50% passing (partial - some tests timeout)
**Automation Rate:** 65% (for FOL conversion)

This document explains why we're not at 100% for either metric and provides the roadmap to get there.

---

## Part 1: Why Not 100% Test Pass Rate?

### Root Cause: DynamicConst in Replacements

**Problem:** Rules with `DynamicConst` in replacements cannot be verified automatically.

**Example:**
```python
class Add_SpecialConstantRule_3(VerifiableRule):
    c1, c2 = Const("c_1"), Const("c_2")
    val_res = DynamicConst("val_res", lambda ctx: ctx['c_2'].value - 1)

    PATTERN = (x ^ c1) + 2*(x | c2)
    REPLACEMENT = x + val_res        # val_res is computed at runtime
    CONSTRAINTS = [when.is_bnot("c_1", "c_2")]
```

**What happens during verification:**
1. Pattern: `(x ^ c_1) + 2*(x | c_2)` ✅ (c_1, c_2 are symbolic)
2. Replacement: `x + val_res` where val_res has `expected_value=None`
3. ast_to_z3_expression calls `ast.value` → returns `None`
4. `z3.BitVecVal(None, 32)` → ERROR or timeout

**Why it fails:**
- DynamicConst computes values at *runtime* during pattern matching
- For *verification*, we need the mathematical relationship
- The lambda `lambda ctx: ctx['c_2'].value - 1` isn't parsed/analyzed

**Affected rules:** 49 out of 162 (30%)
- 27 with DynamicConst only
- 22 with both DynamicConst + constraints

---

### What We Fixed (Commits 21fc195, 9d620c0, 1f119a3)

#### Fix 1: AstConstant.value Property
**Before:**
```python
@property
def value(self):
    assert self.mop is not None and self.mop.t == ida_hexrays.mop_n
    return self.mop.nnn.value
```

**After:**
```python
@property
def value(self):
    if self.mop is None:
        return self.expected_value  # For Z3 verification before matching
    assert self.mop.t == ida_hexrays.mop_n
    return self.mop.nnn.value
```

**Impact:** Fixed verification for rules with concrete constants (ONE, TWO, etc.)

#### Fix 2: Pattern-Matching Constants as Symbolic Variables
**Before:**
```python
# Only created Z3 vars for variables, not constants
var_names = set()
for leaf in leaves:
    if not leaf.is_constant():  # Skipped ALL constants
        var_names.add(leaf.name)
```

**After:**
```python
var_names = set()
const_names = set()
for leaf in leaves:
    if leaf.is_constant():
        if leaf.expected_value is None:  # Pattern-matching constant
            const_names.add(leaf.name)
    else:
        var_names.add(leaf.name)

# Create Z3 vars for BOTH
z3_vars = {**vars, **consts}
```

**Impact:** Rules with `Const("c_1")` now treat them as symbolic, not concrete 0

#### Fix 3: Auto-Convert DSL Constraints to Z3
**Before:**
```python
def get_constraints(self, z3_vars):
    return []  # Always empty!
```

**After:**
```python
def get_constraints(self, z3_vars):
    # Auto-convert when.is_bnot("c_1", "c_2") to: c_1 == ~c_2
    for constraint in self.CONSTRAINTS:
        closure_vars = extract_from_closure(constraint)
        if closure_vars:
            var1, var2 = closure_vars
            yield z3_vars[var1] == ~z3_vars[var2]
```

**Impact:** 49 rules with `is_bnot` constraints now have Z3 constraints applied

#### Fix 4: Const() No Longer Converts None to 0
**Before:**
```python
def Const(name, value=None):
    actual_value = value if value is not None else 0  # BUG!
    return AstConstant(name, actual_value)
```

**After:**
```python
def Const(name, value=None):
    return AstConstant(name, value)  # Pass None as-is
```

**Impact:** Pattern-matching constants now have `expected_value=None`

---

### What Still Fails: DynamicConst Rules

**Rules affected:** 49 (30% of total)

**Example failure:**
```
Rule: Add_SpecialConstantRule_3
Pattern: (x ^ c_1) + 2*(x | c_2)
Replacement: x + val_res

Error: val_res.value = None
       z3.BitVecVal(None, 32) → crash/timeout
```

**Solution requires manual work:**

Each rule with DynamicConst needs its verification formula written manually:

```python
class Add_SpecialConstantRule_3(VerifiableRule):
    # ... existing code ...

    def get_replacement_for_verification(self):
        """Override for Z3 verification only.

        For verification: val_res = c_2 - 1
        For runtime: val_res = DynamicConst(lambda ctx: ctx['c_2'].value - 1)
        """
        return x + (c2 - ONE)  # Mathematical formula for verification
```

Or use a hybrid approach where verification formula is separate:

```python
class Add_SpecialConstantRule_3(VerifiableRule):
    # Pattern matching (runtime)
    PATTERN = (x ^ c1) + 2*(x | c2)
    REPLACEMENT = x + DynamicConst("val_res", lambda ctx: ctx['c_2'].value - 1)

    # Z3 verification (compile-time)
    VERIFICATION_REPLACEMENT = x + (c2 - ONE)  # Use this for verify()
    CONSTRAINTS = [when.is_bnot("c_1", "c_2")]
```

**Estimated effort:** 5 minutes per rule × 49 rules = 4 hours

---

## Part 2: Why Not 100% Automation Rate?

### Lambda Constraints (31 rules)

**Problem:** Arbitrary Python code in lambdas can't be auto-converted to Z3

**Example:**
```python
CONSTRAINTS = [
    lambda ctx: (ctx['c_1'].value & 0xFF) == ctx['c_2'].value
]
```

**To auto-convert, we'd need:**
1. Python AST parser to analyze lambda body
2. Mapping of Python operations → Z3 operations
3. Semantic understanding (what does `& 0xFF` mean in context?)

**Manual conversion:**
```python
def get_constraints(self, z3_vars):
    return [(z3_vars['c_1'] & 0xFF) == z3_vars['c_2']]
```

**Why not automate?**
- 31 rules × 5 minutes = 2.5 hours manual work
- Building AST parser + semantic analysis = 1-2 weeks
- **ROI: Not worth it** for one-time conversion

---

## Roadmap to 100%

### Phase 1: Handle DynamicConst (4 hours)

**Option A: VERIFICATION_REPLACEMENT attribute**
```python
class MyRule(VerifiableRule):
    PATTERN = ...
    REPLACEMENT = x + DynamicConst(...)       # For runtime
    VERIFICATION_REPLACEMENT = x + (c2 - ONE)  # For Z3
```

**Option B: get_replacement_for_verification() method**
```python
def get_replacement_for_verification(self):
    return x + (c2 - ONE)
```

**Effort:**
- Implement infrastructure: 30 minutes
- Convert 49 rules: 4 hours (5 min each)
- **Total: 4.5 hours**

### Phase 2: Handle Lambda Constraints (2.5 hours)

Manually override `get_constraints()` for 31 rules with lambdas.

**Template:**
```python
def get_constraints(self, z3_vars):
    # Original: lambda ctx: (ctx['c_1'].value & 0xFF) == ctx['c_2'].value
    return [(z3_vars['c_1'] & 0xFF) == z3_vars['c_2']]
```

**Effort:** 31 rules × 5 minutes = 2.5 hours

### Phase 3: Fix Known Issues (1 hour)

- 4 expected failures (CstSimplificationRule2, CstSimplificationRule12, Mul_MBA_1/4)
  - Mark as `@pytest.mark.xfail(reason="Known incorrect from main branch")`
- 3-5 genuinely broken rules
  - Debug and fix

**Effort:** 1 hour

---

## Total Effort to 100%

| Phase | Task | Time |
|-------|------|------|
| 1 | DynamicConst infrastructure | 30 min |
| 1 | Convert 49 DynamicConst rules | 4 hours |
| 2 | Convert 31 lambda constraints | 2.5 hours |
| 3 | Fix known issues | 1 hour |
| **Total** | | **8 hours** |

---

## Alternative: FOL DSL Conversion (Recommended)

Instead of fixing the current system, convert to FOL DSL:

**Benefits:**
1. Clean separation: verification vs. pattern matching
2. Explicit DynamicConst handling from the start
3. Multiple backends (Z3, SMT-LIB, Why3, Lean)
4. Better long-term maintainability

**Effort:**
- FOL DSL implementation: 2-3 days
- Rule conversion (65% automated): 2-3 weeks
- **Total: 3-4 weeks**

**Why this is better:**
- Current system has accumulated technical debt
- FOL gives clean slate with proper semantics
- Scales to future verification needs
- Educational value (rules are their own specification)

---

## Recommendation

**Short-term (8 hours):** Fix DynamicConst + lambdas to get to 100% passing tests

**Long-term (3-4 weeks):** Migrate to FOL DSL as documented in `FOL_CONVERSION_FEASIBILITY.md`

The FOL approach is the right architectural decision. The short-term fix is just a bridge if you need immediate results.
