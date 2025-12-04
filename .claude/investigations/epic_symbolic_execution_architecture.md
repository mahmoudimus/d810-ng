# Epic: Symbolic Execution Architecture for Unflattening

**Epic ID**: d810ng-symex
**Status**: Planning
**Created**: 2024-12-04
**Priority**: High

---

## 1. Epic Summary

Determine the correct architectural approach for handling path-sensitive analysis in d810-ng's control flow unflattening, specifically addressing failures in OR-based state machine patterns like `abc_f6_or_dispatch`.

---

## 2. Background Context

### The Problem

`UnflattenerFakeJump` produces incorrect output for OR-based state machines:
- **Expected**: `return a1 | 0xFFu`
- **Actual**: `return 0xFFFFFFFFLL` with `++global_side_effect`

The rule fires (2 uses, 5 patches), but the transformation is wrong.

### Root Cause Analysis (Completed)

1. **MopTracker is path-insensitive**: It explores ALL predecessor combinations during backward search, including paths that can't actually execute.

2. **Spurious paths**: For `abc_f6_or_dispatch`, MopTracker finds 5 histories:
   - 3 resolved (but may include spurious paths with inconsistent values)
   - 2 unresolved (dispatcher back-edges - expected and normal)

3. **The d810-ng heuristic**: Filters unresolved histories, proceeds if `resolved > unresolved`. This is conceptually correct but doesn't check for value consistency among resolved paths.

### Key Insight

The **Flattening Invariant** ("all paths through a predecessor have the same state value") **holds in real execution** but MopTracker's backward search doesn't respect dispatcher routing constraints.

---

## 3. Existing Infrastructure

| Component | Location | Purpose |
|-----------|----------|---------|
| MopTracker | `src/d810/hexrays/tracker.py` | Backward data-flow analysis |
| MicroCodeInterpreter | `src/d810/expr/emulator.py` | Forward concrete execution |
| z3_utils | `src/d810/expr/z3_utils.py` | AstNode → Z3 BitVec conversion |
| mba.backends.z3 | `src/d810/mba/backends/z3.py` | Pure symbolic verification |
| symbolic-microcode-plan.md | `docs/` | Design for SymbolicMicroCodeInterpreter |

**Key**: The infrastructure for Z3-based symbolic execution at microcode level **already exists**. The question is how to use it.

---

## 4. Child Beads

### Bead: Investigation - OR-Based State Machine Failure
**ID**: d810ng-symex-01
**Type**: Research
**Status**: Ready

Determine exactly why filtering unresolved histories fails for OR-based patterns.

### Bead: Decision - Symbolic Execution Approach
**ID**: d810ng-symex-02
**Type**: Decision
**Status**: Blocked by d810ng-symex-01

Choose the architectural approach based on investigation findings.

### Bead: Implementation - Chosen Approach
**ID**: d810ng-symex-03
**Type**: Implementation
**Status**: Blocked by d810ng-symex-02

Implement the chosen solution.

---

## 5. Decision Criteria

The investigation must answer these questions to inform the decision:

### Q1: Value Consistency
Do the resolved histories for `abc_f6_or_dispatch` have **consistent** state values?
- If YES: Problem is downstream (CFG transformation)
- If NO: Problem is spurious paths giving wrong values

### Q2: Where Does It Break?
At what point does the unflattening go wrong?
- MopTracker returns wrong values?
- Filtering selects wrong value?
- CFG transformation misuses correct values?

### Q3: Scope of Problem
How many test cases are affected by this pattern?
- Just `abc_f6_or_dispatch`?
- All OR-based patterns?
- Other patterns too?

### Q4: Minimum Viable Fix
What's the simplest fix that would work?
- Add consistency check to filtering?
- Track dispatcher constraints in MopTracker?
- Full symbolic execution?

---

## 6. Possible Approaches

| Approach | Effort | Risk | Benefit |
|----------|--------|------|---------|
| **A: Consistency Check** | Low | Low | Detects spurious paths, but doesn't fix them |
| **B: Constraint-Aware MopTracker** | Medium | Medium | Prunes spurious paths at source |
| **C: SymbolicMicroCodeInterpreter** | High | Medium | Full forward symbolic execution |
| **D: Revert to d810 behavior** | Low | Low | Quick fix, may miss valid cases |

---

## 7. Success Criteria

1. `abc_f6_or_dispatch` produces correct output: `return a1 | 0xFFu`
2. No regression in other test cases
3. Clear architectural documentation
4. Truth DB updated with verified facts

---

## 8. References

- Knowledge doc: `.claude/knowledge/moptracker_symbolic_execution.md`
- Design doc: `docs/symbolic-microcode-plan.md`
- Handoff: `.claude/handoffs/2025-12-04-unflattenerfakejump-regression.md`
- Test case: `samples/src/c/abc_f6_constants.c`
