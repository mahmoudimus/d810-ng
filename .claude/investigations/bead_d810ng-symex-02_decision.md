# Bead: Decision - Symbolic Execution Approach

**Bead ID**: d810ng-symex-02
**Epic**: d810ng-symex (Symbolic Execution Architecture)
**Type**: Decision
**Status**: Blocked (waiting for d810ng-symex-01)
**Created**: 2024-12-04

---

## 1. Objective

Choose the correct architectural approach for handling path-sensitive analysis in d810-ng based on the investigation findings from d810ng-symex-01.

---

## 2. Decision Framework

### Input Required

From d810ng-symex-01:
- Are resolved values consistent or inconsistent?
- Where exactly does the transformation fail?
- How many test cases are affected?

### Decision Matrix

| Finding | Recommended Approach |
|---------|---------------------|
| Values consistent, transformation wrong | Fix CFG transformation logic |
| Values inconsistent, few cases | Add consistency check + fallback |
| Values inconsistent, many cases | Constraint-aware MopTracker |
| Complex path interactions | SymbolicMicroCodeInterpreter |

---

## 3. Approach Options

### Option A: Consistency Check (Lightweight)

**What**: Add a check after filtering to verify all resolved values agree.

```python
resolved_values = [h.get_value(state_var) for h in resolved_histories]
if len(set(resolved_values)) > 1:
    logger.warning("Inconsistent values: %s", resolved_values)
    return 0  # Bail out
```

**Pros**:
- Minimal code change
- Fails safe (doesn't transform when uncertain)
- Quick to implement

**Cons**:
- Doesn't fix the underlying issue
- May cause false negatives (bail when it shouldn't)

**When to use**: If investigation shows inconsistent values are rare edge cases.

---

### Option B: Constraint-Aware MopTracker (Medium)

**What**: Modify MopTracker to track dispatcher constraints and prune invalid paths.

```python
# When entering a case block from dispatcher
constraint = (state_var == case_value)

# When exploring backward through dispatcher, only follow
# predecessors consistent with the constraint
```

**Pros**:
- Fixes the root cause (spurious paths)
- Stays within existing MopTracker architecture
- No new major components

**Cons**:
- Requires understanding MopTracker deeply
- May have edge cases
- Medium complexity

**When to use**: If investigation shows spurious paths are the main issue.

---

### Option C: SymbolicMicroCodeInterpreter (Full)

**What**: Implement the design from `docs/symbolic-microcode-plan.md`.

- Forward symbolic execution with Z3 BitVecs
- Path constraint collection at branches
- Z3 solver for feasibility checking
- Fallback when concrete execution fails

**Pros**:
- Most general solution
- Handles any pattern
- Documented design exists

**Cons**:
- Highest effort (1 week+)
- New code to maintain
- Potential performance impact

**When to use**: If multiple patterns need path-sensitive analysis.

---

### Option D: Revert to d810 Behavior (Quick Fix)

**What**: Change `continue` back to `return 0` when unresolved histories exist.

```python
if not all([h.is_resolved() for h in histories]):
    return 0  # Original d810 behavior
```

**Pros**:
- One-line change
- Known to work in original d810
- No risk of new bugs

**Cons**:
- May miss valid optimizations
- Doesn't improve on d810
- Doesn't address root cause

**When to use**: If investigation shows the d810-ng heuristic is fundamentally flawed.

---

## 4. Evaluation Criteria

| Criterion | Weight | Description |
|-----------|--------|-------------|
| **Correctness** | 40% | Produces correct output for all patterns |
| **Simplicity** | 25% | Minimal code changes, easy to understand |
| **Maintainability** | 20% | Easy to debug and extend |
| **Performance** | 15% | Doesn't significantly slow deobfuscation |

---

## 5. Decision Template

After investigation completes, fill in:

```markdown
## Decision Record

### Date: [YYYY-MM-DD]

### Investigation Summary
- Resolved values consistent: [YES/NO]
- Failure point: [MopTracker/Filtering/CFG Transform]
- Affected cases: [count]

### Chosen Approach: [A/B/C/D]

### Rationale
[Why this approach fits the findings]

### Trade-offs Accepted
[What we're giving up by choosing this approach]

### Implementation Plan
[Link to d810ng-symex-03]
```

---

## 6. Dependencies

- **Blocked by**: d810ng-symex-01 (investigation results)
- **Blocks**: d810ng-symex-03 (implementation)

---

## 7. Stakeholder Input

Questions for discussion before finalizing:

1. How important is handling OR-based patterns? (Common in real obfuscators?)
2. Is there appetite for larger architectural changes?
3. What's the acceptable performance budget for symbolic execution?
