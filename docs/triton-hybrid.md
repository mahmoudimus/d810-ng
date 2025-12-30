## Triton Hybrid Integration Plan (Selective Symbolic Oracle)

This document describes how to integrate Triton as an optional, on‑demand symbolic oracle alongside the existing `MicroCodeInterpreter`. The goal is to keep the current fast path intact, and query Triton only when we hit unknowns that matter (branches, indirect jumps, or key memory loads), avoiding fabricated values like synthetic call returns.

### Why integrate a Triton hybrid

- • Avoid wrong concretization: Your microcode emulator sometimes must pick a number (0 or a sentinel) for unknowns (e.g., call results, `%var_*` bases). That cascades into bad states like `MEMORY[0]` and misfolded branches.
- • Keep unknowns symbolic: Triton models call results and FS/GS/PEB reads as symbolic with constraints (e.g., “!= 0”), so we don’t fabricate addresses or segments.
- • Prove only when safe: Use SMT to prove/negate conditions. If undecidable quickly, leave unknown. This preserves correctness without sacrificing performance.

### Where it’s helpful

- • PE header probe branch
  - Example: `jnz xdu.4([ds:%var_658].2), #0x5A4D`
  - Current issue: `%var_658` is unknown → risky to fold; sometimes collapses to `$0x0`.
  - With Triton: treat `[ds:%var_658]` as a symbolic load; ask “is it always 0x5A4D?” If provable, fold; if refutable, invert; else leave unknown. No fake zeros.

- • PEB/TEB-based derefs
  - Example: `ldx ds, (NtCurrentPeb()+0x18), %var_...`
  - Current issue: forcing 0/None leads to `MEMORY[0]` or “no segment”.
  - With Triton: `NtCurrentPeb()` is a non-zero symbolic pointer; deref stays symbolic unless needed for a proof. Avoids null/segment artifacts.

- • Dispatcher next-target resolution (flattening)
  - Example: indirect jump via `state = tbl[(state ^ key) & mask]`.
  - With Triton: enumerate a small, feasible set of ijmp targets under constraints; feed them to CFG expansion to recover real successors.

- • Guarded constant folds with unknown inputs
  - Example: `((sym & 0xFF00) == 0x4D00)` for MZ/PE checks.
  - With Triton: prove bitmask relations directly; fold only when the solver guarantees it.

- • Eliminating MEMORY[0] regressions
  - Null derefs and synthetic call addresses aren’t manufactured; symbolic memory + constraints prevents spurious `[0x0]` reads and keeps conditions correct.

- • Lightweight, on-demand oracle
  - Triton runs only on small “micro-slices” at the moment you need a decision (branch fold, target set, or specific load), with tight timeouts and fast fallback to your emulator.

In short: the hybrid keeps your emulator fast and deterministic for the easy cases, while using Triton to safely reason about the hard unknowns that currently force incorrect constants or missed optimizations.

### What we keep vs. add

- Keep: `MicroCodeInterpreter` concrete fast path and all existing passes.
- Add: a tiny `SymbolicOracle` wrapper (Triton-backed) that can:
  - prove/negate a branch condition,
  - evaluate a memory load when the base is symbolic,
  - enumerate a small set of targets for an indirect jump/state variable.

### Design principles

- Optional and safe: if Triton is missing or times out, fall back to current behavior.
- Narrow scope: map only micro-ops needed for dispatcher reasoning (mov, add/sub, and/or/xor, shifts, zero/sign extend, `ldx`, and compare). Calls become symbolic values, not numbers.
- No synthetic constants: calls and FS/GS/PEB helpers are modeled as symbolic with non-zero constraints. We do not fabricate segment-backed addresses.
- Tight limits: per-query solver timeout (50–100 ms), step cap (~100), and path cap (~64). Abort quickly if not decisive.

---

## Files to add

- `src/d810/expr/sym_oracle_triton.py` — Triton wrapper (optional import, minimal API)
- (Optional) `src/d810/expr/sym_ir.py` — small adapters to convert a micro-slice to Triton ops

No changes are required in other modules to land the scaffolding. Hooks in the emulator and unflattener are guarded and off by default.

---

## Public API of the oracle

```python
class SymbolicOracle:
    def __init__(self, arch: str = "auto", timeout_ms: int = 80,
                 step_cap: int = 100, path_cap: int = 64): ...

    def is_enabled(self) -> bool:
        """Return True if Triton is available and the context is initialized."""

    def prove(self, micro_slice, condition) -> tuple[bool|None, dict]:
        """Return (True, model) if condition is valid; (False, model) if unsat; (None, {}) if unknown.
        `micro_slice` is a minimal list of defining micro-ops for operands in `condition`."""

    def eval_load(self, micro_slice, addr_expr, size: int) -> int|None:
        """Attempt to concretize a memory load at `addr_expr` under current constraints.
        Return int on singleton model; else None."""

    def enumerate_ijmp_targets(self, micro_slice, max_targets: int = 8) -> list[int]|None:
        """Enumerate a small set of feasible indirect jump targets; None if not decisive."""
```

---

## Example implementation skeleton

```python
# src/d810/expr/sym_oracle_triton.py
from __future__ import annotations

try:
    from triton import TritonContext, ARCH, Instruction, AST_REPRESENTATION
    from triton import MemoryAccess, CPUSIZE
except Exception:  # Triton not available
    TritonContext = None


class SymbolicOracle:
    def __init__(self, arch: str = "auto", timeout_ms: int = 80,
                 step_cap: int = 100, path_cap: int = 64):
        self.timeout_ms = timeout_ms
        self.step_cap = step_cap
        self.path_cap = path_cap
        self.ctx = None
        if TritonContext is None:
            return
        self.ctx = TritonContext()
        # Choose architecture dynamically or from config
        if arch == "x64":
            self.ctx.setArchitecture(ARCH.X86_64)
        elif arch == "x86":
            self.ctx.setArchitecture(ARCH.X86)
        elif arch == "aarch64":
            self.ctx.setArchitecture(ARCH.AARCH64)
        else:
            # Heuristic or config-driven selection could go here
            self.ctx.setArchitecture(ARCH.X86_64)
        self.ctx.setAstRepresentation(AST_REPRESENTATION.PYTHON)

    def is_enabled(self) -> bool:
        return self.ctx is not None

    # --- helpers ---
    def _fresh_symbolic(self, name: str, size_bits: int, non_zero: bool = False):
        var = self.ctx.newSymbolicVariable(size_bits, name)
        sym = self.ctx.getAstContext().variable(var)
        if non_zero:
            self.ctx.pushPathConstraint(sym != 0)
        return sym

    def _build_slice(self, micro_slice):
        """Translate a minimal subset of micro-ops into Triton AST.
        Intentionally partial: mov, add/sub, and/or/xor, shifts, zext/sext, ldx (symbolic), cmps.
        Calls: treated as fresh symbolic with optional non-zero constraints for FS/GS/PEB.
        """
        # Implementation intentionally left minimal for the first iteration.
        # Map only the operations required by the dispatcher condition/targets.
        pass

    # --- API ---
    def prove(self, micro_slice, condition):
        if not self.is_enabled():
            return (None, {})
        try:
            self._build_slice(micro_slice)
            cond_ast = condition.to_triton_ast(self.ctx)  # adapter method you provide
            # Check validity: cond is valid iff not (¬cond) is satisfiable
            is_invalid = self.ctx.isSat(~cond_ast)
            if not is_invalid:  # ¬cond unsat => cond valid
                return (True, {})
            # Check refutation: cond is unsat?
            if not self.ctx.isSat(cond_ast):
                return (False, {})
            return (None, {})
        except Exception:
            return (None, {})

    def eval_load(self, micro_slice, addr_expr, size: int):
        if not self.is_enabled():
            return None
        try:
            self._build_slice(micro_slice)
            addr_ast = addr_expr.to_triton_ast(self.ctx)
            # Try to model a singleton value: ask solver for a model, re-check uniqueness if needed
            if not self.ctx.isSat(addr_ast == addr_ast):  # trivial satisfiable check
                return None
            model = self.ctx.getModel(addr_ast)
            if not model:
                return None
            # For first iteration, only handle fully concrete address
            addr_val = addr_ast.evaluate()
            if addr_val is None:
                return None
            # We do not read real process memory; only constant tables you pre-seed can be read.
            return None
        except Exception:
            return None

    def enumerate_ijmp_targets(self, micro_slice, max_targets: int = 8):
        if not self.is_enabled():
            return None
        try:
            self._build_slice(micro_slice)
            # Build target expr and enumerate up to max_targets models (skipped in skeleton)
            return None
        except Exception:
            return None
```

Notes:

- The above skeleton intentionally defers the micro-slice to Triton mapping. Start with the few ops used by your dispatcher and grow as needed.
- For helpers like `__readfsqword`/`__readgsqword`/`NtCurrentPeb`, create a fresh symbolic pointer with a `!= 0` constraint. Do not fabricate numbers.

---

## Emulator hooks (guarded, optional)

Add a nullable `oracle` field to `MicroCodeInterpreter` and delegate only when unknowns matter:

```python
# in __init__
self.oracle = None  # type: Optional[SymbolicOracle]

# on evaluating call (m_call/m_icall)
if self.oracle and self.oracle.is_enabled():
    # return a placeholder object representing a symbolic value in your env,
    # instead of a fabricated integer
    return environment.define_symbolic_call_result(ins, non_zero_for_helpers=True)

# on evaluating load (mop_d) when base is unknown/symbolic
if self.oracle and self.oracle.is_enabled() and self.symbolic_mode:
    oracle_val = self.oracle.eval_load(micro_slice, addr_expr, size)
    if oracle_val is not None:
        return oracle_val & AND_TABLE[size]
    return None  # keep unknown

# on folding branch conditions
if self.oracle and self.oracle.is_enabled():
    verdict, _ = self.oracle.prove(micro_slice, cond_expr)
    if verdict is True:
        return True  # taken
    if verdict is False:
        return False  # not taken
    # else keep unknown
```

These hooks are no-ops unless `oracle` is assigned and enabled.

---

## Using the oracle in the unflattener

- In `tracker.py` / `optimizers/microcode/flow/flattening/generic.py`, when the dispatcher’s state variable or an indirect jump target set is unknown:

```python
if interpreter.oracle and interpreter.oracle.is_enabled():
    targets = interpreter.oracle.enumerate_ijmp_targets(micro_slice, max_targets=8)
    if targets:
        # feed targets into the CFG expansion logic
        ...
```

---

## Configuration and defaults

- Add a config option (e.g., `conf/options.json`):
  - `symbolic_oracle.enabled: false`
  - `symbolic_oracle.timeout_ms: 80`
  - `symbolic_oracle.step_cap: 100`
  - `symbolic_oracle.path_cap: 64`

When disabled or Triton is unavailable, behavior remains identical to today.

---

## Installation notes (optional)

- Triton often requires system deps (Capstone, Z3). On macOS:
  - `brew install capstone z3`
  - `pip install triton-library`
- Keep this optional. Ship with try/except guards so the package works without Triton.

---

## Milestones

1) Scaffolding (this doc + `sym_oracle_triton.py` skeleton)
2) Minimal mapping: mov/add/sub/xor/and/shifts, zero/sign-extend, compares; calls as symbolic; FS/GS/PEB non-zero.
3) Hook branch folding: `prove` integration (timeouts enforced).
4) Hook indirect jump: `enumerate_ijmp_targets` with small bound.
5) Caching: memoize per-EA micro-slice results.

Each milestone yields value and can be merged independently.

## Extra Consideration

Triton is a better fit for this use-case than angr.

- When Triton is better
  - Lightweight, embeddable “oracle” for small micro-slices.
  - Easy to introduce symbolic vars for calls and prove/negate branch conditions.
  - Low overhead, keeps your Hex-Rays microcode context and mappings intact.

- When angr is better
  - Whole-function/path exploration, richer OS/library models (SimProcedures), full calling convention handling.
  - You want to symbolically execute from bytes with its own IR and memory model, not inline with Hex-Rays.

- Integration cost
  - Triton: map a small subset of micro-ops; add non-zero constraints for FS/GS/PEB helpers; query with tight timeouts.
  - angr: heavy; requires lifting to VEX or feeding raw bytes, syncing memory/state with IDA, and you lose the neat 1:1 link to Hex-Rays microcode.

Recommendation: keep your fast MicroCodeInterpreter and add a selective Triton-backed oracle for unknowns at branches/ijmp/critical loads. Consider angr only if you later need broader path exploration with complex library/OS semantics.

---

## Extra Notes on Architecture and Implementation

### How the Emulator Cascades Through Both Passes

This section documents the actual architecture discovered through code analysis:

#### Pass 1: `generic.py` (Dispatcher Emulation) — Direct Emulator Use

```
GenericDispatcherInfo.emulate_dispatcher_with_father_history()
    ↓
Creates: MicroCodeInterpreter(symbolic_mode=True)
         MicroCodeEnvironment()
    ↓
Iterates through dispatcher blocks:
    MicroCodeInterpreter.eval_instruction(blk, ins, environment)
    ↓ Executes each instruction, updates environment
    ↓ When hit unknown → synthetic value or fails
```

**Key insight:** This pass uses `MicroCodeInterpreter` **directly** with `symbolic_mode=True`, allowing it to continue emulation even with unknowns (by fabricating synthetic values). Triton oracle here provides **proven values instead of guesses**.

#### Pass 2: `fix_pred_cond_jump_block.py` (Branch Prediction) — Indirect Emulator Use via Backward Tracing

```
sort_predecessors(blk)
    ↓
MopTracker.search_backward(pred_blk, pred_blk.tail)
    ↓ Traces backward, builds list of MopHistory objects (one per path)
    ↓
get_all_possibles_values(mop_histories, searched_mop_list)
    ↓ For each history, calls: mop_history.get_mop_constant_value(searched_mop)
    ↓
MopHistory._execute_microcode()
    ↓ Line 113: Creates MicroCodeInterpreter(symbolic_mode=False)
    ↓ Lines 190-201: Iterates through all instructions on that path
    ↓ Each instruction: microcode_interpreter.eval_instruction(blk, ins, environment)
    ↓ Result: Returns None if any instruction can't be evaluated
```

**Key insight:** This pass uses `MicroCodeInterpreter` **indirectly through `MopHistory`** with `symbolic_mode=False`, meaning **any unknown stops the backward trace** (returns `None`). Triton oracle here provides **fallback values that prevent trace failure**.

### The Critical Difference: symbolic_mode

| Context | Mode | Behavior | Triton Benefit |
|---------|------|----------|---|
| **generic.py** | `symbolic_mode=True` | Hits unknown → uses synthetic value, continues | Oracle avoids synthetic by proving real value |
| **MopHistory** | `symbolic_mode=False` | Hits unknown → returns None, trace fails | Oracle provides concrete value so trace succeeds |

### Implementation Considerations

#### For `generic.py` (Immediate Priority)

Add oracle to `MicroCodeInterpreter` as documented in the triton-hybrid.md skeleton. The `symbolic_mode=True` path already handles unknowns gracefully (just replaces them with synthetics). Triton improves this by:

1. **Proving branch conditions:** Instead of taking both paths symbolically, Triton can prove only one is feasible
2. **Modeling system helpers:** `__readfsqword`, `__readgsqword`, `NtCurrentPeb` become symbolic with `!= 0` constraint (never fabricates 0)
3. **Resolving dispatcher state:** When initial state is unknown, Triton can symbolically execute dispatcher to collect feasible exit blocks

#### For `fix_pred_cond_jump_block.py` (Secondary, Optional Enhancement)

To leverage Triton in this pass, you have two options:

**Option A: Enable oracle fallback in `MopHistory` (Recommended)**

```python
# In tracker.py, line 113:
self._mc_interpreter = MicroCodeInterpreter(
    symbolic_mode=False,
    oracle=triton_oracle  # NEW
)

# In emulator.py eval() method, add:
if value is None and self.oracle and self.oracle.is_enabled():
    # Try oracle as last resort before raising
    value = self.oracle.query_register_value(mop)
```

**Benefit:** `MopHistory` can complete backward traces even with unknowns, improving branch prediction confidence.

**Risk:** Minimal — oracle is only queried on unknowns, so no regression.

**Option B: Use `symbolic_mode=True` in `MopHistory` (Advanced)**

```python
# In tracker.py, line 113:
self._mc_interpreter = MicroCodeInterpreter(
    symbolic_mode=True,  # NEW
    oracle=triton_oracle  # NEW
)
```

**Benefit:** Backward traces naturally handle unknowns via Z3 bitvectors.

**Risk:** Code expecting concrete `int` values might break; requires careful value handling.

**Recommendation:** Start with Option A (minimal change). If you find that backward traces still fail frequently, revisit Option B.

### Phase-Based Rollout Strategy

1. **Phase 1 (Unflattening):** Triton in `generic.py` only
   - Adds oracle to `MicroCodeInterpreter.__init__()` with `oracle=None` default
   - Improves dispatcher emulation for cases with unknowns
   - `fix_pred_cond_jump_block.py` behavior unchanged (still uses `MopHistory` without oracle)

2. **Phase 2 (Branch Prediction, Optional):** Triton fallback in `MopHistory`
   - Add oracle field to `MopHistory`
   - In `eval()` method, query oracle as fallback on unknowns
   - Improves backward traces that currently fail at unknowns

3. **Phase 3 (Optimization, Optional):** Full symbolic mode in `MopHistory`
   - Switch `MopHistory` to `symbolic_mode=True` if Phase 2 shows diminishing returns
   - Requires testing and validation

### Key Data Flow Paths for Triton

**Dispatcher Emulation (forward execution):**
```
Unknown register/memory
  ↓ (symbolic_mode=True)
  ↓ MicroCodeInterpreter.eval()
  ↓ (no value in environment)
  ↓ [NEW] Query oracle.prove_value(mop) if enabled
  ↓ If oracle returns value: use it + cache in environment
  ↓ Else: use synthetic (current behavior)
```

**Backward Tracing (backward path analysis):**
```
MopHistory._execute_microcode() hits unknown
  ↓ (symbolic_mode=False)
  ↓ MicroCodeInterpreter.eval_instruction() returns False
  ↓ _execute_microcode() returns False
  ↓ get_mop_constant_value() returns None
  ↓ [NEW, Phase 2] Query oracle.get_concrete_value(mop) in MopHistory
  ↓ If oracle returns value: use it + cache in environment
  ↓ Else: still None (current behavior)
```

### Testing Strategy

**Unit tests to add:**

1. **Oracle availability:** Verify graceful degradation when Triton unavailable
2. **Dispatcher emulation:** Validate that dispatcher with symbolic inputs correctly identifies exit blocks
3. **Backward tracing:** Verify that MopHistory can complete paths with oracle fallback
4. **Branch prediction:** Confirm that fix_pred_cond_jump_block improves with oracle (Phase 2+)

**Integration tests:**

1. Real binaries with obfuscated dispatchers
2. Binaries with unknown call results in dispatcher paths
3. Binaries with FS/GS/PEB-based guards in branch conditions
4. Regression testing: ensure Phase 1 doesn't break existing passes

### Performance Considerations

**Oracle query costs:**

- Per-branch solve timeout: 50–100ms (configurable)
- Typical benefit: 1–10 queries per dispatcher (for branch proofs)
- Expected overhead: <500ms per dispatcher emulation
- Expected benefit: 2–5× more dispatchers successfully unflattened

**Mitigation strategies:**

- Cache results by dispatcher signature
- Skip oracle on fast paths (concrete-only evaluation)
- Use tight timeouts and step caps as documented
- Monitor in logs; adjust timeouts if needed

### Debugging and Logging

Add logging at oracle query points:

```python
# In MicroCodeInterpreter.eval()
if self.oracle and self.oracle.is_enabled():
    logger.debug("Querying oracle for %s (unknown in env)", format_mop_t(mop))
    value = self.oracle.query_value(...)
    if value is not None:
        logger.info("Oracle proved value for %s: %x", format_mop_t(mop), value)
    else:
        logger.debug("Oracle inconclusive for %s", format_mop_t(mop))
```

This makes it easy to identify which unknowns Triton helps with and which still need heuristics.
