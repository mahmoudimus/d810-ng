# Bead: OR-Based State Machine Failure Investigation

**Bead ID**: d810ng-symex-01
**Epic**: d810ng-symex (Symbolic Execution Architecture)
**Type**: Research/Investigation
**Status**: Ready
**Created**: 2024-12-04

---

## 1. Objective

Determine **exactly** why `UnflattenerFakeJump` produces incorrect output for OR-based state machine patterns, with specific focus on `abc_f6_or_dispatch`.

---

## 2. Investigation Plan

### Phase 1: Trace the Actual Execution

**Goal**: Capture what MopTracker actually returns for `abc_f6_or_dispatch`.

**Method**:
1. Add debug logging to `UnflattenerFakeJump.analyze_blk()`
2. Run deobfuscation on `abc_f6_or_dispatch`
3. Capture:
   - All histories returned by MopTracker
   - Which are resolved vs unresolved
   - The actual values found for each resolved history
   - Which values are selected after filtering

**Questions to answer**:
- Are the 3 resolved values consistent (all same value)?
- Or do they differ (indicating spurious paths)?

### Phase 2: Trace the CFG Transformation

**Goal**: Understand what happens after value resolution.

**Method**:
1. Add logging to the CFG transformation code
2. Trace what patches are applied
3. Compare expected vs actual CFG changes

**Questions to answer**:
- What block redirections are performed?
- Are they correct based on the resolved values?
- Where does the `++global_side_effect` come from?

### Phase 3: Compare with Working Cases

**Goal**: Find what's different about OR-based patterns vs working patterns.

**Method**:
1. Run same analysis on a known-working case (e.g., standard `state = CONST` pattern)
2. Compare the MopTracker output
3. Identify the divergence point

**Questions to answer**:
- Do working cases always have consistent resolved values?
- What's the ratio of resolved:unresolved for working vs failing cases?

### Phase 4: Root Cause Identification

**Goal**: Pinpoint the exact failure mechanism.

Based on Phases 1-3, determine which of these is the root cause:

| Hypothesis | How to Verify |
|------------|---------------|
| **H1**: Spurious paths give inconsistent values | Check if resolved values differ |
| **H2**: Wrong value selected from consistent set | Check filtering logic |
| **H3**: Correct value but wrong transformation | Check CFG patch application |
| **H4**: Something else entirely | Debug further |

---

## 3. Test Commands

```bash
# Run specific test with verbose output
PYTHONPATH=src pytest tests/system/cases/libobfuscated_comprehensive.py -k "abc_f6_or_dispatch" -v --tb=long

# Run with d810 debug logging (requires adding logging)
D810_DEBUG=1 pytest tests/system/cases/libobfuscated_comprehensive.py -k "abc_f6_or_dispatch" -v
```

---

## 4. Files to Instrument

| File | What to Log |
|------|-------------|
| `src/d810/optimizers/microcode/flow/flattening/unflattener_fake_jump.py` | All histories, values, filtering decisions |
| `src/d810/hexrays/tracker.py` | Path exploration, resolution status |
| `src/d810/optimizers/microcode/flow/flattening/generic.py` | CFG transformations |

---

## 5. Expected Outputs

### Deliverable 1: MopTracker Output Analysis

```markdown
## MopTracker Results for abc_f6_or_dispatch

### Block X Analysis (dispatcher conditional)
| History | Path | Resolved? | State Value | Notes |
|---------|------|-----------|-------------|-------|
| 0 | ... | Yes | 0x... | ... |
| 1 | ... | No | - | Back-edge |
| ... | ... | ... | ... | ... |

### Value Consistency
- All resolved values same: [YES/NO]
- If NO, values found: [list]
```

### Deliverable 2: Root Cause Report

```markdown
## Root Cause Analysis

### Failure Mechanism
[Detailed explanation]

### Evidence
[Specific log output / values showing the failure]

### Minimum Fix Required
[What needs to change to fix this]
```

---

## 6. Success Criteria

- [ ] Captured actual MopTracker output for `abc_f6_or_dispatch`
- [ ] Identified whether resolved values are consistent
- [ ] Traced CFG transformation to find where it goes wrong
- [ ] Documented root cause with evidence
- [ ] Proposed minimum viable fix

---

## 7. Dependencies

- Requires IDA Pro environment for system tests
- Uses existing test infrastructure

---

## 8. Next Steps After Completion

Results feed into **d810ng-symex-02** (Decision bead) to choose the architectural approach.
