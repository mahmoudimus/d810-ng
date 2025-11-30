## Triton-backed dispatcher emulation: hybrid fast-path + symbolic fallback

This document describes how to augment the current dispatcher evaluation in the control-flow unflattener with a Triton-powered symbolic fallback, while preserving the existing MicroCodeInterpreter fast path. The goal is to improve robustness on unknown inputs, indirect jumps, and jump-tables, without paying solver costs for common cases.

References:

- Triton repository: `https://github.com/JonathanSalwan/Triton`
- Triton Python API docs: `https://triton-library.github.io/documentation/doxygen/py_triton_page.html`
- Triton examples (Python): `https://github.com/JonathanSalwan/Triton/tree/master/src/examples/python`

### Current architecture snapshot (integration points)

- Dispatcher discovery and unflattening live under `src/d810/optimizers/microcode/flow/flattening/`.
- Emulation entry point used by unflattener:
  - `GenericDispatcherInfo.emulate_dispatcher_with_father_history()` in `generic.py` builds a `MicroCodeEnvironment`, seeds variables from `MopHistory`, and steps through blocks with `MicroCodeInterpreter.eval_instruction(...)` to find the first out-of-dispatcher block and collect side effects.
  - Call site example:
    - `GenericDispatcherUnflatteningRule.resolve_dispatcher_father()` calls `dispatcher_info.emulate_dispatcher_with_father_history(...)` and rewrites CFG accordingly.
- The concrete evaluator is `d810.expr.emulator.MicroCodeInterpreter` with `MicroCodeEnvironment`.

Key file references:

- `src/d810/optimizers/microcode/flow/flattening/generic.py` (dispatcher logic)
- `src/d810/hexrays/tracker.py` (`MopHistory`, provides initial values)
- `src/d810/expr/emulator.py` (current concrete microcode interpreter)

### Problem statement

Concrete microcode evaluation can stall when:

- Values for state variables or memory reads are unknown.
- Control flow uses `m_jtbl`/`m_ijmp` or computed branches with data-dependent targets.
- Helpers or FS/GS/PEB/TEB-derived values require modeling.

We want a symbolic fallback to answer feasibility and compute the next dispatcher successor, without fully replacing the fast path.

## Proposed approach

Add a Triton-based fallback in `GenericDispatcherInfo.emulate_dispatcher_with_father_history()` that is invoked only when the concrete path becomes unknown or ambiguous.

High-level flow:

1. Attempt current concrete emulation via `MicroCodeInterpreter` (unchanged).
2. If it returns unknown/halts before exiting dispatcher region, invoke Triton fallback.
3. Triton executes native instructions from the current block head EA, with a seeded state derived from `MopHistory`, until the execution exits the dispatcher region. On conditional/indirect branches, solver queries determine feasible successors.
4. Return the same outputs as today: the first out-of-dispatcher `mblock_t` plus any non-CF side effects to be copied.

### Dispatcher region identification

Use the existing `GenericDispatcherInfo` fields to constrain the Triton run:

- `entry_block` identifies the entry `mblock_t` and its `use_before_def_list`.
- `dispatcher_internal_blocks` and `dispatcher_exit_blocks` delimit the region. Continue stepping while current block serial is in the internal set and stop once not in it.

### Triton environment construction

Triton context configuration (example for x86_64):

- `ARCH.X86_64`
- Modes: `ALIGNED_MEMORY = True`, others as needed
- Solver timeout: 50–100ms per query (configurable)

State seeding from father history:

- For each mop in `entry_block.use_before_def_list`, obtain value from `father_history.get_mop_constant_value(mop)`.
  - If known: set concrete Triton register or memory value.
  - If unknown: symbolize the register or memory cell.

Register mapping:

- Map IDA/Hex-Rays register names to Triton registers (e.g., `rax`, `rbx`, `rcx`, `rdx`, `rsi`, `rdi`, `rsp`, `rbp`, XMM/YMM if needed). Provide a small adapter table.

Stack and memory model:

- Choose a synthetic stack base (e.g., `0x7fff00000000`) for stack variables (`mop_S`) and model `off` as an address offset from that base. Size according to mop size.
- For `mop_v` and other absolute address reads:
  - If the target segment is non-writable, concretize from IDA (`idaapi.get_qword/get_dword/...`).
  - If writable or not found: symbolize the memory cell.

Helpers and special reads:

- For helpers like `__readfsqword`, `__readgsqword`, and known PEB/TEB accessors, inject stable non-zero concrete values (consistent with today’s `_get_synthetic_call_ret`).
- Optionally for unknown helpers, stub with a fresh symbol constrained to be non-zero.

### Stepping and control-flow resolution

Instruction fetch/decoding:

- Fetch bytes at current EA from IDA, decode with IDA to get size and next EA; feed bytes to Triton `Instruction` and call `ctx.processing(inst)`.
- Maintain `EA → block_serial` mapping via `get_block_serials_by_address(mba, ea)` when needed.

Branches:

- For conditional branches, retrieve the branch condition AST and query feasibility for both taken/not-taken. Pick the successor block that remains within the dispatcher region if unique; if multiple feasible successors remain inside, pick a deterministic one (e.g., lowest serial) and log.
- For `jtbl`/indirect jumps: obtain the computed target AST; for each candidate case target block EA, assert equality and query; select a feasible target in the region. If default or multiple, use a deterministic tie-breaker.

Exit condition:

- Stop when the next block serial is not in the internal dispatcher set; return that `mblock_t`.
- Collect non-control-flow side-effect instructions during traversal for later copying (mirrors current behavior).

### Caching and performance

Cache key:

- `(entry_block_entry_ea, dispatcher_id, compared_mop signature, initial_value_digest)`

Cache value:

- `(out_block_serial, side_effects_fingerprint)` or a small structure with resolved branch sequence.

Timeouts and limits:

- Per-solve timeout: 50–100ms; per-dispatcher budget: 300–500ms (configurable).
- If exceeded, abort fallback and bubble up “unresolvable” so the outer logic can keep current behavior.

### Configuration and flags

- Add config knobs (with sensible defaults) to `conf/options.json` or the relevant optimizer config:
  - `use_triton_fallback`: true/false
  - `triton_timeout_ms`: int
  - `triton_max_total_ms`: int
  - `triton_concretize_readonly`: bool
  - `triton_symbolize_writable`: bool

Import guard:

- Attempt to import Triton at runtime; if unavailable, keep current behavior silently.

### Error handling

- If decode fails at an EA, try stepping to block tail and transition to successor by IDA CFG; otherwise abort fallback.
- If solver returns unknown/timeout for all options, abort fallback.
- Always keep concrete fast path as the first attempt; never regress current success cases.

## Deliverables and code edits

1. New module: `src/d810/optimizers/microcode/flow/flattening/triton_fallback.py`
   - `build_triton_context(arch_config) -> TritonContext`
   - `seed_state_from_mops(ctx, mba, mops, father_history) -> SeedReport`
   - `step_until_exit(ctx, mba, entry_blk, internal_serials, exit_serials, helpers_policy) -> (target_blk, side_effects)`
   - `dispatch_with_triton(...)` convenience function used by `GenericDispatcherInfo`.

2. Edit `GenericDispatcherInfo.emulate_dispatcher_with_father_history(...)`:
   - Wrap existing concrete run.
   - On failure/unknown inside dispatcher, call the fallback when `use_triton_fallback` and Triton available.
   - Return consistent outputs.

3. Config: extend relevant config file(s) with flags/timeouts and thread through `GenericDispatcherUnflatteningRule.configure`.

4. Telemetry/logging: emit timing and solver stats under `unflat_logger` at info/debug.

## Testing strategy

Unit tests:

- Seed-only tests for `seed_state_from_mops` mapping register and stack variables (including unknowns → symbols).
- Branch feasibility unit tests with small synthetic blocks: conditional, `jtbl`, and `ijmp`.

System tests:

- Reuse existing dispatcher fixtures; run with fallback disabled (baseline) vs enabled and assert identical target block selections on known solvable cases.
- Add cases where the concrete path previously failed due to unknowns (e.g., writable memory read); verify fallback resolves to a stable out-of-dispatcher block and unflattening proceeds.

Performance:

- Record dispatcher-resolution latency and cache hit rate. Ensure typical budgets stay under configured thresholds.

## Risks and mitigations

- Semantic gap native vs microcode: we drive by native instructions while the rest of pipeline uses microcode. Mitigate by only using Triton to decide the next block; do not mutate microcode based on Triton state.
- Over-constraining vs under-constraining: prefer symbolization for writable/unknown reads. Concretize only RO segments.
- Solver churn: use timeouts and caching; short-circuit when only one in-region successor is feasible.

## Rollout plan

1. Land behind `use_triton_fallback=false` by default; CI green.
2. Enable in developer testing, collect logs, tune timeouts.
3. Enable by default once stability and perf are confirmed.

## Appendix: Pseudocode sketch

```python
def emulate_dispatcher_with_father_history(...):
    # 1) Try fast path
    if concrete_run_succeeds:
        return target_blk, side_effects

    # 2) Optional fallback
    if not config.use_triton_fallback or not triton_available:
        return cur_blk, executed  # existing behavior

    # 3) Triton path
    ctx = build_triton_context()
    seed_state_from_mops(ctx, mba, entry_block.use_before_def_list, father_history)
    target_blk, side_effects = step_until_exit(ctx, mba, entry_block, internal_blocks, exit_blocks)
    return target_blk, side_effects
```
