## Symbolic microcode evaluator plan (Z3/Triton-AST), preserving Hex-Rays semantics

This document proposes a symbolic variant of the existing MicroCodeInterpreter that builds and solves symbolic expressions for dispatcher evaluation. It retains Hex-Rays microcode semantics and API while enabling SMT solving of conditional/indirect branches and unknown reads.

Rationale:
- Avoid the native-vs-microcode semantic gap by staying within microcode opcodes and `mop_t` abstractions.
- Leverage Z3 (preferred, already present in repo) or Triton ASTs to reason about unknowns and control-flow feasibility.

Relevant code today:
- `src/d810/expr/emulator.py`: concrete `MicroCodeInterpreter` and `MicroCodeEnvironment`.
- `src/d810/optimizers/microcode/flow/flattening/generic.py`: dispatcher orchestration; calls `GenericDispatcherInfo.emulate_dispatcher_with_father_history()`.
- `src/d810/hexrays/tracker.py`: `MopHistory` produces initial mop values; used to seed environment.
- `src/d810/expr/z3_utils.py`: existing helpers for Z3 integration that we can reuse.


## Design overview

Two compatible evaluators:
- Keep the current concrete `MicroCodeInterpreter` as-is (fast path).
- Introduce `SymbolicMicroCodeInterpreter` with the same public surface (or nearly):
  - `eval_instruction(blk, ins, env, ...) -> bool`
  - `eval_mop(mop, env, ...) -> ValueLike | None`
  - Internally, operations produce Z3 bit-vectors instead of Python ints when needed.

Backend abstraction (optional but recommended for clarity):
- Define a small adapter that implements primitive arithmetic and logical ops over either ints or Z3 bit-vectors. Example methods: `bv(size, int)`, `add`, `sub`, `mul`, `udiv`, `sdiv`, `and_`, `or_`, `xor`, `shl`, `lshr`, `ashr`, `eq`, `ult`, `ule`, `ugt`, `uge`, `slt`, `sle`, `sgt`, `sge`, `ite`.
- Concrete backend maps to Python ints with masking; symbolic backend maps to Z3 `BitVecRef` with the same bit-width.

Value representation:
- Use bit-width-accurate values everywhere. Ensure masking with `AND_TABLE[size]` semantics is preserved in the symbolic domain via explicit `Extract/ZeroExt/SignExt` as needed.

Environment model:
- `MicroCodeEnvironment` keeps separate maps for `mop_r` and `mop_S`. For the symbolic interpreter, store `ValueLike` (int or Z3 BitVec) instead of ints.
- For `mop_v` (absolute memory):
  - If segment non-writable: concretize via IDA read (fast, precise constant).
  - If writable or segment unknown: return fresh Z3 symbol (bit-vector) keyed by EA and size, cached per environment to stay consistent.

Unknowns and symbols:
- When a mop’s value is not found in the environment, create a fresh Z3 symbol (e.g., `sym_r_rax_8`, `sym_S_off_0x30_8`, `sym_mem_0x401000_4`).
- For reads with helper-like semantics already special-cased in the concrete evaluator (`__readfsqword`, `__readgsqword`, PEB/TEB, etc.), either:
  - direct concrete non-zero (mirrors current behavior), or
  - symbolic value with constraint `!= 0` if that is more robust; both are acceptable.


## Opcode coverage

Mirror the existing coverage in `MicroCodeInterpreter._eval_instruction` and `eval`:
- Unary: `m_neg`, `m_lnot`, `m_bnot`, `m_low`, `m_high`, `m_xds`, `m_xdu`.
- Binary: `m_add`, `m_sub`, `m_mul`, `m_udiv`, `m_sdiv`, `m_umod`, `m_smod`, `m_or`, `m_and`, `m_xor`, `m_shl`, `m_shr`, `m_sar`.
- Flag ops: `m_cfadd`, `m_ofadd`, `m_set*` (implement using Z3 helpers; reuse `get_add_cf`, `get_add_of`, `get_parity_flag` by re-implementing them over Z3 or writing Z3 equivalents—bit-precise definitions).
- Loads/stores: `m_ldx`/`m_stx` symbolic handling as above; stack loads (`ss.2`) remain as environment lookups; other segments → RO concretize or symbolize.
- Control flow:
  - For conditional jumps, evaluate the predicate as a Z3 Bool and fork potential successors.
  - For `m_jtbl`, evaluate key expression (symbolic) and compare against cases: build disjunctions of `(key == case_value)` then map to block targets.
  - For `m_ijmp`, evaluate destination address expression; check equality against candidate target block entry EAs.


## Branch feasibility and next-block selection

Strategy:
- When a branch is encountered inside the dispatcher region, construct solver queries to determine successor feasibility.
- If exactly one in-region successor is feasible, take it.
- If multiple are feasible, apply a deterministic policy (lowest serial), and optionally record the condition for cache.
- If none feasible or solver times out, abort symbolic mode and propagate “unresolvable”.

Solving infrastructure:
- Use `src/d810/expr/z3_utils.py` helpers to manage contexts and timeouts.
- Per-branch solve timeout: 50–100ms; overall per-dispatcher budget: 300–500ms (configurable).


## Integration with the unflattener

`GenericDispatcherInfo.emulate_dispatcher_with_father_history(...)`:
1. Keep current concrete run with `MicroCodeInterpreter`.
2. If that fails to exit the dispatcher region or meets unresolved evaluation:
   - If `use_symbolic_microcode=true`, instantiate `SymbolicMicroCodeInterpreter` and re-run from entry.
   - Use the same initial seeding from father history into the symbolic environment.
   - Step within dispatcher region, deciding successors via Z3 feasibility.
3. Return `(target_blk, instructions_executed)` with the same shape as today.

Minimal API alignment:
- `SymbolicMicroCodeInterpreter.eval_instruction(...)` should update an environment’s `next_blk` and `next_ins` akin to today (internally it will select the feasible successor). If both successors are feasible, it chooses deterministically and records a note (for logs or caching).


## Caching and determinism

Cache key:
- `(entry_block_serial, compared_mop signature, initial_value_digest, maturity)`

Cache content:
- `(resolved_successor_serial, path_conditions_digest)`

Determinism:
- Always choose the lowest-serial feasible successor when multiple are possible; log all feasible ones for debugging.


## Configuration

Add optimizer options (e.g., in `conf/options.json` or relevant unflattening config):
- `use_symbolic_microcode`: bool (default false)
- `z3_timeout_ms`: int
- `z3_total_budget_ms`: int
- `symbolize_writable_reads`: bool (default true)
- `concretize_readonly_reads`: bool (default true)


## Error handling and fallbacks

- If symbolic interpreter encounters an unsupported opcode, fall back to concrete interpreter for that step when safe; otherwise bail out of symbolic mode.
- On timeout/unknown, abort symbolic mode and bubble up.


## Deliverables and code edits

New module(s):
- `src/d810/expr/symbolic_interpreter.py`:
  - `class SymbolicMicroCodeInterpreter:` mirrors `MicroCodeInterpreter` public API
  - Small Z3 backend or reuse/adapt from `z3_utils.py`
  - Helpers for symbolic flag computation

Edits:
- `src/d810/optimizers/microcode/flow/flattening/generic.py`:
  - In `GenericDispatcherInfo.emulate_dispatcher_with_father_history`, add optional symbolic fallback.
- `src/d810/conf/options.json` (or specific rule config) to include the new flags.


## Testing strategy

Unit tests (symbolic ops):
- Arithmetic/bitwise ops produce correct Z3 AST widths and masks.
- `m_high`/`m_low` and `xds/xdu` correctly transform bit-widths.
- Flag computations (`cf`, `of`, parity) verified via small satisfiability checks.

Branch tests:
- Conditional branch with symbolic predicate: verify solver picks the feasible successor.
- Jump table with few cases: verify feasibility selection and default handling.
- Indirect jump: equality to candidate block addresses decides successor.

System tests:
- Reuse existing dispatcher fixtures; compare outcomes (target block + CFG rewrites) with and without the symbolic fallback on known-resolvable flows.
- Add cases that require symbolic reasoning (writable memory load, unknown register) to validate improved robustness.

Performance:
- Enforce per-branch and per-dispatcher time budgets; ensure overall optimizer runtime stays within acceptable bounds.


## Risks and mitigations

- Incomplete opcode coverage: start with the subset exercised by dispatcher paths; log and add as needed.
- Z3 path explosion: we only need the next successor, not full path exploration; solve locally at each branch with short timeouts.
- Masking/width mistakes: centralize bit-width handling and add unit tests.


## Rollout plan

1. Land behind `use_symbolic_microcode=false` and run tests.
2. Dogfood on representative binaries; grow opcode coverage guided by logs.
3. Consider enabling by default if success rate and perf are good; otherwise keep as opt-in for tough samples.


## Appendix: Implementation notes

- Bit-widths:
  - Use `size` (bytes) → `bits = size * 8`; ensure every operation returns correctly masked values (`Extract(bits-1, 0, expr)` as needed).
- Memory symbols:
  - Key by `(ea, size)` and cache in the environment so repeated loads from the same address are the same symbol.
- Dispatcher boundaries:
  - Only perform symbolic branching while `cur_blk.serial` belongs to the dispatcher internal set to avoid wandering beyond intended scope.
