# Migration Verification Workflow

## Purpose
Systematically verify that code migrations (refactorings, DSL conversions, etc.) are exact and complete by comparing against the source/original implementation.

## When to Use
- Migrating lambda constraints to declarative DSL
- Refactoring pattern matching rules
- Converting imperative code to declarative
- Any transformation claiming "parity" or "equivalence"

## Workflow

### 1. Identify Source of Truth
Find the original/reference implementation:
```bash
# For main branch files
git show origin/main:path/to/file.py

# For test specifications
grep -r "RuleName" tests/
```

**Key files for d810-ng rule migration:**
- Main branch: `src/d810/optimizers/microcode/instructions/pattern_matching/rewrite_*.py`
- Z3 constraints: `tests/unit/optimizers/test_z3_simplifications.py`
- Test specs: Look for `RuleInfo(name="RuleName", ...)`

### 2. Extract Complete Specifications
For EACH failing rule, extract:

**A. Pattern and Replacement:**
```python
# From main branch .py file
PATTERN = ...  # or property
REPLACEMENT_PATTERN = ...
```

**B. Runtime Constraints:**
```python
# From main branch check_candidate() method
def check_candidate(self, candidate):
    # Extract ALL conditions here
    if condition1:
        return False
    if condition2:
        return False
    # Extract derived constant calculations
    candidate.add_constant_leaf("name", calculation, size)
```

**C. Z3 Verification Constraints:**
```python
# From test_z3_simplifications.py
"expression => replacement": lambda _, V: [
    # ALL constraints needed for Z3 proof
    constraint1,
    constraint2,
    V["derived"] == calculation,
]
```

### 3. Compare Systematically
Create a checklist for EACH rule:

```
Rule: RuleName
□ Pattern matches exactly
□ Replacement matches exactly
□ All runtime constraints migrated (check_candidate)
□ All Z3 constraints migrated
□ Derived constant formulas match
□ Operator choices match (XOR vs OR for disjoint sets)
□ Test passes
```

### 4. Common Migration Errors

**Missing Constraints:**
- Lambda constraints not converted to declarative
- Additional Z3 constraints discovered during verification
- Implicit conditions from check_candidate

**Wrong Operators:**
- Using `^` (XOR) instead of `|` (OR) for disjoint masks
- Using `^` instead of `+` for summation

**Incorrect Formulas:**
- Missing terms in derived constants (e.g., `c ^ d` vs `c ^ d ^ ~e`)
- Wrong REPLACEMENT expression

### 5. Verification Commands

**Test single rule:**
```bash
pytest tests/unit/optimizers/test_verifiable_rules.py::TestVerifiableRules::test_rule_is_correct[RuleName] -v
```

**Test group of fixed rules:**
```bash
pytest tests/unit/optimizers/test_verifiable_rules.py -k "Rule1 or Rule2 or Rule3" -v
```

**Full suite:**
```bash
pytest tests/unit/optimizers/test_verifiable_rules.py -v 2>&1 | tee results.txt
```

### 6. Analysis of Failures

When a rule fails Z3 verification:

**A. Check if constraints match main:**
```bash
# Extract main branch Z3 constraints
git show origin/main:tests/unit/optimizers/test_z3_simplifications.py | grep -A 10 "RuleName"
```

**B. Manual verification with counterexample:**
```python
# Use Z3's counterexample to verify manually
values = {'x': ..., 'c1': ..., ...}  # From error message
pattern_result = evaluate_pattern(values)
replacement_result = evaluate_replacement(values)
print(f"Equal? {pattern_result == replacement_result}")
```

**C. If still failing after matching all constraints:**
- Rule definition itself is mathematically incorrect
- Report to original author/tests

### 7. Documentation Template

When fixing a rule, document:
```python
class RuleName(VerifiableRule):
    """Original docstring

    Requires:
    - constraint1 (from check_candidate)
    - constraint2 (discovered in Z3 verification)
    """

    CONSTRAINTS = [
        # Check X (from check_candidate line Y)
        declarative_constraint1,
        # Newly discovered required condition (from Z3 verification)
        declarative_constraint2,
        # Definition of derived constant
        c_res == formula,  # Comment explaining why OR vs XOR
    ]
```

### 8. Batch Processing Strategy

For multiple failing rules:

1. **Group by failure type:**
   - Missing constraints
   - Wrong operators
   - Size-dependent (requires special handling)

2. **Fix groups in order:**
   - Quick wins: missing declarative constraints
   - Medium: operator fixes
   - Hard: size-dependent (may need new DSL features)

3. **Test after each group:**
   ```bash
   pytest -k "fixed_rule1 or fixed_rule2" -v
   ```

4. **Commit incrementally:**
   ```bash
   git commit -m "fix: batch X - description"
   ```

## Example: CstSimplificationRule20

**Source of truth:**
```python
# Main branch check_candidate:
if candidate["c_and_1"].value & candidate["c_and_2"].value != 0:
    return False

# Z3 constraints (test_z3_simplifications.py):
(V["c_and_1"] & V["c_and_2"]) == 0,  # From check_candidate
(V["c_xor"] & (V["c_and_1"] | V["c_and_2"])) == 0,  # Discovered
V["c_and_res"] == V["c_and_1"] | V["c_and_2"],  # OR not XOR!
```

**Migrated version:**
```python
CONSTRAINTS = [
    when.is_bnot("x_0", "bnot_x_0"),
    (c_and_1 & c_and_2) == ZERO,  # From check_candidate
    (c_xor & (c_and_1 | c_and_2)) == ZERO,  # From Z3
    c_and_res == c_and_1 | c_and_2,  # OR for disjoint masks
    c_xor_res == c_and_1 ^ c_xor,
]
```

## Checklist Before Declaring "Done"

- [ ] All failing tests identified
- [ ] Each failure compared against main branch
- [ ] All constraints from main migrated
- [ ] All tests passing
- [ ] Commit messages document what was found/fixed
- [ ] No regressions (run full suite)
