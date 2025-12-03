# Refactoring D810

> **Last Updated**: 2025-11-30
> **Status**: DSL complete, Hodur complete, **Test coverage BLOCKING further refactoring**

This document tracks the architectural refactoring of D810-ng, consolidating the original refactoring plan with the microcode unflattening modernization work.

---

## Executive Summary

| Work Stream | Status | Completion |
|-------------|--------|------------|
| Declarative DSL + Z3 Verification | ✅ Complete | 100% |
| Hodur State Machine Unflattening | ✅ Complete | 100% |
| **Flattening Module Test Coverage** | 🚨 **BLOCKING** | ~50% → 85% |
| Composition over Inheritance | ⏸️ Paused | 72% |
| Persistent Caching Architecture | ❌ Deferred | 10% |

### Critical Blocker

**No more refactoring until test coverage reaches 85-90%.** We've been running into regressions because the flattening module (~7,300 LOC across 17 files) lacks adequate test coverage. Tests must:
1. Exercise all rules and code paths
2. Verify correctness (not just "it runs")
3. Catch regressions before they reach production

---

## Part 1: Declarative DSL Refactoring ✅ COMPLETE

### Problem

The original `AstNode` construction was imperative and low-level:

```python
# Before (Imperative) - Hard to read, error-prone
PATTERN = AstNode(m_sub, AstNode(m_or, AstLeaf("x"), AstLeaf("y")),
                  AstNode(m_and, AstLeaf("x"), AstLeaf("y")))
```

### Solution

A declarative DSL using Python's operator overloading with automatic Z3 verification:

```python
# After (Declarative) - Readable, self-verifying
x, y = Var("x_0"), Var("x_1")

class XorFromOrAndSub(VerifiableRule):
    PATTERN = (x | y) - (x & y)
    REPLACEMENT = x ^ y
```

### Achievements

| Metric | Target | Achieved |
|--------|--------|----------|
| Rules migrated | 181 | **183** |
| Z3 verified | >90% | **95.6%** (175/183) |
| Test time | <30s | **<1s** |
| IDA-independent | Yes | **Yes** |

### Architecture

```
src/d810/mba/                    # IDA-independent package
├── dsl.py                       # SymbolicExpression with operator overloading
├── constraints.py               # Constraint system with .to_int()
├── verifier.py                  # VerificationEngine protocol
├── rules/                       # All 183 optimization rules
│   ├── __init__.py              # RuleRegistry with lazy instantiation
│   ├── _base.py                 # VerifiableRule base class
│   ├── xor.py, add.py, ...      # Rules by operation type
│   └── hodur.py                 # Hodur-specific patterns
└── backends/
    ├── z3.py                    # Z3 verification (pure Python)
    ├── ida.py                   # IDA adapter
    └── egglog_backend.py        # Experimental e-graph
```

### Skipped Rules (8 total)

**Known incorrect (5)**: `AndGetUpperBits_FactorRule_1`, `CstSimplificationRule2`, `CstSimplificationRule12`, `Mul_MBA_2`, `Mul_MBA_3`

**Performance (2)**: `Mul_MBA_1`, `Mul_MBA_4` (nonlinear, slow to verify but correct)

**Context-aware (1)**: `ReplaceMovHighContext` (requires IDA context)

---

## Part 2: Hodur State Machine Unflattening ✅ COMPLETE

### Problem

Hodur malware uses nested `while(1)` loops instead of O-LLVM's switch-case dispatcher:

| Feature | O-LLVM | Hodur |
|---------|--------|-------|
| Dispatcher | Single `switch` with `m_jtbl` | Nested `while(1)` loops |
| Comparison | `switch(var)` → jump table | `jnz var, CONST` |
| State var | Usually register | Usually stack (`mop_S`) |

The existing `FixPredecessorOfConditionalJumpBlock` caused **cascading unreachability**: redirecting entry blocks made the entire dispatcher unreachable, collapsing 196 lines to 7.

### Solution

1. **Dispatcher detection heuristic**: Skip blocks where ≥90% of predecessors go same direction
2. **HodurUnflattener**: Dedicated state machine unflattener using hybrid detection
3. **DeferredGraphModifier**: Queue CFG changes, apply in batch for stability

### Achievements

| Metric | Before | After |
|--------|--------|-------|
| Runtime | 8.3s | **~1s** (8x faster) |
| While loops | 12 | **0** |
| Output lines | 196 | **103** (clean) |

### Files

- `unflattener_hodur.py` (873 LOC) - Main unflattener
- `dispatcher_detection.py` (877 LOC) - DispatcherCache, DispatcherAnalysis
- `heuristics.py` (517 LOC) - DispatcherHeuristics
- `fix_pred_cond_jump_block.py` (492 LOC) - Fixed with dispatcher heuristic

### State Variable Detection (Implemented)

Hybrid approach combining:
1. CFG structure analysis (dispatcher by predecessor count)
2. Constant propagation (variables with many large constants)
3. Frequency scoring (comparison × assignment frequency)
4. Dataflow verification

---

## Part 3: Flattening Module Test Coverage 🚨 BLOCKING

### Why This Is Blocking

**We cannot continue refactoring without adequate test coverage.** Recent work has introduced regressions that weren't caught because:
- Many code paths are untested
- Tests verify "it runs" but not "it's correct"
- No regression tests for edge cases

### Module Overview

The flattening module is **7,314 LOC** across 17 Python files:

| File | LOC | Current Coverage | Priority |
|------|-----|------------------|----------|
| `generic.py` | 1,594 | ~60% | P1 - Core |
| `dispatcher_detection.py` | 877 | ~40% | P1 - Core |
| `unflattener_hodur.py` | 873 | ~50% | P1 - Core |
| `services.py` | 785 | ~25% | P1 - New code |
| `heuristics.py` | 517 | ~25% | P1 - Critical |
| `fix_pred_cond_jump_block.py` | 492 | ~40% | P2 |
| `abc_block_splitter.py` | 460 | ~30% | P2 |
| `unflattener_badwhile_loop.py` | 323 | ~40% | P2 |
| `unflattener.py` | 289 | ~50% | P2 |
| `unflattener_refactored.py` | 284 | ~31% | P2 - New code |
| `loop_prover.py` | 272 | ~40% | P2 |
| `unflattener_fake_jump.py` | 167 | ~20% | P3 |
| `unflattener_indirect.py` | 122 | ~30% | P3 |
| `unflattener_single_iteration.py` | 118 | ~40% | P3 |
| `unflattener_switch_case.py` | 79 | ~50% | P3 |
| `utils.py` | 62 | ~60% | P3 |
| **TOTAL** | **7,314** | **~50%** | **Target: 85%** |

### Coverage Target

| Metric | Current | Target |
|--------|---------|--------|
| Line coverage | ~50% | **85%** |
| Branch coverage | ~40% | **80%** |
| All rules exercised | No | **Yes** |
| Correctness verified | Partial | **Yes** |

### Test Strategy

#### 1. Unit Tests (No IDA Required)

Test pure logic in isolation using mocks:

```python
# tests/unit/optimizers/microcode/flow/flattening/test_heuristics.py
class TestDispatcherHeuristics:
    def test_predecessor_ratio_detection(self):
        """≥90% same-direction predecessors → skip block"""
        mock_block = create_mock_block(predecessors=10, same_direction=9)
        assert DispatcherHeuristics.should_skip(mock_block) == True

    def test_state_variable_scoring(self):
        """High comparison + assignment frequency → likely state var"""
        candidates = [
            {'var': 'v17', 'comparisons': 15, 'assignments': 12},
            {'var': 'v5', 'comparisons': 2, 'assignments': 1},
        ]
        best = score_candidates(candidates)
        assert best['var'] == 'v17'
```

#### 2. System Tests (Requires IDA)

Test against real obfuscated binaries:

```python
# tests/system/cases/test_flattening_patterns.py
class TestFlatteningPatterns:
    @pytest.mark.parametrize("binary,func,expected_patches", [
        ("ollvm_obfuscated.dll", "flatten_switch", 15),
        ("hodur_sample.dll", "state_machine", 39),
        ("tigress_sample.dll", "indirect_dispatch", 8),
    ])
    def test_unflattening_correctness(self, binary, func, expected_patches):
        """Verify correct number of patches applied"""
        result = run_unflattener(binary, func)
        assert result.patches_applied >= expected_patches
        assert result.while_loops_remaining == 0
```

#### 3. Regression Tests

Snapshot tests to catch behavioral changes:

```python
# tests/system/cases/test_regressions.py
class TestRegressions:
    def test_no_cascading_unreachability(self):
        """Hodur regression: FixPredecessor shouldn't collapse dispatchers"""
        result = decompile("hodur_sample.dll", "state_machine")
        assert result.line_count > 50  # Was collapsing to 7 lines
        assert "while" not in result.output  # No residual while loops
```

### Open Issues (from beads)

| Issue | File | Current → Target |
|-------|------|------------------|
| d810ng-6lt | services.py | 25% → 85% |
| d810ng-xfr | heuristics.py | 25% → 85% |
| d810ng-lh5 | unflattener_refactored.py | 31% → 85% |
| d810ng-73h | loop_prover.py | 40% → 85% |
| d810ng-48i | unflattener_single_iteration.py | 40% → 85% |
| d810ng-irj | unflattener_fake_jump.py | 20% → 85% |
| d810ng-ade | Fix legacy test failures (4 tests) | - |
| d810ng-kk4 | Fix nested dispatcher tests (2 failing) | - |
| d810ng-ldk | Fix dispatcher pattern tests (4 failing) | - |
| d810ng-2kh | Fix constant folding tests (2 failing) | - |
| d810ng-viv | Fix Approov pattern tests (2 failing) | - |

### Exit Criteria

Before resuming refactoring (Part 4), ALL of the following must be true:

- [ ] Overall line coverage ≥ 85%
- [ ] All 16 failing tests fixed
- [ ] Each unflattener rule has at least one correctness test
- [ ] Regression tests exist for Hodur, O-LLVM, and Tigress patterns
- [ ] CI passes on all tests

---

## Part 4: Composition over Inheritance ⏸️ PAUSED (72%)

> **Status**: Paused until Part 3 (test coverage) is complete.

### Problem

Deep inheritance hierarchies create God objects:

```
Unflattener → GenericDispatcherUnflatteningRule → GenericUnflatteningRule → FlowOptimizationRule
```

- **775 LOC** in single class
- **21 methods**, **10+ state variables**
- Implicit state (`self.mba`, `self.cur_maturity`)
- Mixed concerns (find/emulate/patch)

### Solution

Decompose into composable, testable services:

```python
class UnflattenerRule(OptimizationRule):
    def __init__(self):
        self._finder = OLLVMDispatcherFinder()
        self._emulator = PathEmulator()
        self._patcher = CFGPatcher()

    def apply(self, context: OptimizationContext, blk: mblock_t) -> int:
        dispatchers = self._finder.find(context)
        for disp in dispatchers:
            target = self._emulator.resolve_target(context, pred, disp)
            self._patcher.redirect_edge(context, pred, target)
```

### Progress

| Component | File | LOC | Status |
|-----------|------|-----|--------|
| Core Abstractions | `core.py` | 143 | ✅ Complete |
| CFGPatcher | `services.py` | ~200 | ✅ Complete |
| PathEmulator | `services.py` | ~150 | ✅ Complete |
| OLLVMDispatcherFinder | `unflattener_refactored.py` | ~220 | ✅ Complete |
| Unit Tests | - | 0 | ⏸️ Blocked by Part 3 |
| Integration | - | 0 | ⏸️ Blocked by Part 3 |

**Total**: 1241/1727 LOC (72%)

### What's Missing (After Part 3)

1. **Unit tests** for services (CFGPatcher, PathEmulator, DispatcherFinder)
2. **Integration** into main optimizer loop
3. **Migration** from `GenericDispatcherUnflatteningRule`

The refactored code exists but is **not yet wired up**. Original God object still in use.

---

## Part 5: Persistent Caching Architecture ❌ DEFERRED

### Original Plan

A SQLite-backed cache for:
- Dispatcher metadata and skip sentinels
- Merkle tree fingerprints for change detection
- Binary patch descriptions
- Ctree snapshots

### Current State

**Not implemented.** The plan described an ideal architecture but:
- `DispatcherCache` in `dispatcher_detection.py` is **session-only** (in-memory)
- No SQLite persistence
- No Merkle tree diffing
- No parallel emulation framework

### Why Deferred

1. Hodur optimization achieved 8x speedup without caching
2. Session-only caching sufficient for current use cases
3. Higher-priority work (DSL, Hodur, test coverage) takes precedence

### Future Work (If Needed)

```python
# Planned but not implemented
class PersistentMicrocodeCache:
    def __init__(self, db_path: str):
        self.conn = sqlite3.connect(db_path)

    def get_dispatcher_info(self, block_hash: str) -> Optional[DispatcherInfo]: ...
    def set_skip_sentinel(self, block_hash: str) -> None: ...
    def get_merkle_root(self, func_hash: str) -> Optional[str]: ...
```

---

## Recommended Next Steps

### 🚨 Priority 1: Test Coverage (BLOCKING)
1. Fix all 16 failing tests
2. Add unit tests for `heuristics.py`, `services.py`
3. Add system tests for each unflattener rule
4. Add regression tests for known edge cases
5. **Target: 85% coverage before any refactoring**

### Priority 2: Complete Composition Refactoring (After P1)
1. Write unit tests for CFGPatcher, PathEmulator
2. Integrate `UnflattenerRule` into optimizer loop
3. Deprecate `GenericDispatcherUnflatteningRule`

### Priority 3 (Optional): Persistent Caching
Only if session performance becomes a bottleneck on large binaries.

---

## Key Lessons Learned

1. **Declarative > Imperative**: `(x | y) - (x & y)` beats nested `AstNode()` calls
2. **Z3 catches bugs**: Automatic verification found 5 incorrect rules
3. **Separation of concerns**: Services (find/emulate/patch) are independently testable
4. **Deferred patching**: Queue CFG changes to avoid mid-iteration corruption
5. **Heuristics matter**: 90% predecessor check prevents cascading unreachability
6. **Don't over-engineer**: Session-only caching was sufficient; SQLite persistence wasn't needed
7. **Test before refactor**: Regressions without tests are silent failures
8. **Protocols for isinstance()**: Never use `isinstance(obj, ConcreteClass)` in hot-reloadable code - class identity changes between reloads. Use `@runtime_checkable Protocol` for structural typing instead.

---

## How to Add a New Rule

```python
# src/d810/mba/rules/example.py
from d810.mba.dsl import Var, Const
from d810.mba.rules import VerifiableRule

x, y = Var("x_0"), Var("x_1")

class MyRule(VerifiableRule):
    """(x | y) - (x & y) => x ^ y"""
    PATTERN = (x | y) - (x & y)
    REPLACEMENT = x ^ y
    CONSTRAINTS = []  # Optional Z3 constraints

# Test: pytest tests/unit/mba/test_verifiable_rules.py -k MyRule
```

If Z3 verification passes, the rule is mathematically proven correct.
