Plan Summary: Microcode Unflattening Modernisation

Overview

The d810‐ng project contains a Hex‑Rays/IDA plugin that detects and dismantles control‑flow flattening schemes by traversing a function's micro‑code, identifying dispatcher blocks and recovering the original control flow.  The original implementation performed a full scan of every basic block, recomputed def/use information on each pass and lacked any persistence: if IDA was closed, the entire unflattening process had to be repeated.  The goal of this work was to rethink and modernise the architecture so that it runs faster, scales across cores and saves its results across sessions.  This document explains the plan we adopted, the assumptions and reasoning behind each design choice, and the high‑level testing strategy to validate the new features.

Problem Statement and Assumptions
	1.	Expensive exploration – The existing unflattening rule explored every basic block and instruction, even though only a subset of blocks (those with a dispatch mechanism) need full analysis.  We assumed that most blocks are not dispatchers, and that we can quickly detect this from their micro‑code opcodes without decoding all instructions.  If a block is obviously not a candidate, we can skip it immediately.
	2.	Repeated computation – During unflattening, the plugin builds def/use lists for each instruction and re‑emulates dispatcher loops to track state.  We assumed that for a given binary, def/use information and dispatcher behaviour are deterministic and need not be recomputed if the underlying bytes have not changed.
	3.	Non‑persistent micro‑code – IDA does not persist micro‑code or decompiler caches across sessions.  We assumed we can create our own stable fingerprint for a micro‑code block or function using only information available from the mba_t object (such as the opcode sequence and block serial numbers) and that this fingerprint remains valid as long as the binary does not change.
	4.	Parallelisable work – Each function in a binary can be analysed independently.  We assumed it would be safe to process multiple functions in parallel without interfering with IDA's state (provided that each worker has its own micro‑code objects) and that concurrency would provide a measurable speed‑up.
	5.	Integration constraints – Some of the advanced features (e.g., applying binary patches and snapshotting ctrees) require IDA's APIs and cannot be fully exercised in an isolated test environment.  We assumed the plugin would run in IDA, but for unit tests we would stub out or simulate these operations.

Architectural Ideas and Rationale

1. Stable Hashing and Fingerprinting

To determine whether a block or function has changed between runs, we compute a SHA‑256 hash of the opcodes in a block.  For a block with no instructions, we use its serial number as a fallback.  We then combine these block hashes into a function hash and build a Merkle tree over the list of blocks.  The root hash of the tree provides a stable fingerprint for the entire function.  If the root hash has not changed since the last analysis, we can skip the function entirely.  Merkle trees also let us pinpoint which blocks changed, so we can selectively recompute dispatcher information if finer granularity is needed in the future.

Why: Without hashing, the plugin has no way to know whether micro‑code has been previously analysed.  A Merkle tree offers both a constant‑time function identity (via its root) and a logarithmic diff mechanism.  Using cryptographic hashes ensures collisions are extremely unlikely.

2. Persistent Caching via SQLite

We added a lightweight SQLite‑backed cache that stores results keyed by block or function hash.  The cache holds:
	•	Dispatcher metadata – for each candidate block, whether it is a dispatcher, and if so, the list of exit blocks and the final state after emulation.
	•	Skip sentinels – for blocks determined not to be dispatchers, so we do not test them again.
	•	Function processed markers – to record that a function has been analysed and its Merkle root at that time.
	•	Merkle trees – serialised tree structures to compare on subsequent runs.
	•	Patch descriptions – sequences of "replace", "delete" and "rename" actions that describe how to modify the micro‑code or binary to remove flattening.
	•	Ctree snapshots – serialised decompiler output so that the simplified C‑like representation can be restored instead of recomputing it.

Why: The cache decouples the lifetime of the analysis from the IDA session.  Without it, every restart would cause the plugin to re‑scan all blocks and re‑emulate dispatchers.  SQLite is a single portable file that can be copied or backed up and works well with Python's built‑in sqlite3 module.

3. Selective Scanning via Heuristics

We defined a set of candidate entry opcodes (CFF_ENTRY_OPCODES) that includes all conditional jump opcodes and the m_jtbl (switch‑table) opcode.  In the GenericDispatcherCollector, we added a flag skip_non_entry_blocks.  When visiting a block, we quickly scan its instruction list; if none of the opcodes belong to CFF_ENTRY_OPCODES, the block is marked as a non‑dispatcher in the cache and is not further explored.

Why: Flattening dispatchers typically start with a conditional jump or jump table to select the next case.  Blocks lacking such opcodes cannot be dispatchers and thus should be skipped.  This simple heuristic avoids the cost of fully analysing most blocks and has negligible false negatives.

4. Def/Use Memoisation

We introduced a global _DEF_USE_CACHE mapping from block hash to the tuple of def and use lists produced by InstructionDefUseCollector.  In GenericDispatcherBlockInfo.parse(), before computing def/use information, we check this cache; if entries exist, we reuse them.

Why: Building def/use lists for each instruction can be expensive, especially in large functions.  Because these lists only depend on the block's micro‑code (and not on the control flow), caching by block hash ensures we never repeat this work.

5. Parallel Emulation Framework

We added a process_functions_in_parallel() method in the pipeline that uses a ThreadPoolExecutor to process multiple mba_t objects concurrently.  Each worker calls process_function(), which performs hashing, caching, unflattening, patch recording and snapshotting for one function.  An optional max_workers parameter lets the user control the degree of parallelism.

Why: Many binaries contain hundreds or thousands of functions, but unflattening each function is independent.  Using threads (or processes in a future extension) leverages multi‑core CPUs to reduce overall runtime.  Threading is feasible because IDA's micro‑code structures are not shared across functions and because we minimise shared state by using thread‑safe caching primitives.

6. Binary Patching and Ctree Snapshotting

In patching.py, we added classes to record patch actions (e.g., replacing the dispatcher block with a jump to its first case) and to apply them.  Currently the BinaryPatcher uses placeholders for IDA API calls; in an IDA environment it would rewrite the binary or micro‑code accordingly.

In ctree_snapshot.py, we provided functions to serialise a decompiler ctree (cfunc_t) into JSON and to restore it later.  After unflattening, the pipeline stores a snapshot keyed by the function hash.  On subsequent runs, if the function hash matches, the pipeline can present the stored ctree directly to the user instead of running the decompiler again.

Why: Flattening unconditionally destroys a function's natural control flow.  Once we unflatten a dispatcher, we wish to make that transformation permanent.  Binary patching ensures that IDA will re‑analyse the simplified control flow even if the micro‑code cache is cleared.  Ctree snapshotting is less invasive but avoids re‑running the decompiler; it is useful when patching the binary is undesirable (e.g., read‑only firmware).  Both mechanisms illustrate how to persist high‑level results.

Summary of Changes Made
	1.	Modularisation – Added new modules: cache.py (persistent store and block/function hashing), merkle.py (Merkle tree implementation), patching.py (patch actions), ctree_snapshot.py (snapshotting helpers) and pipeline.py (orchestrator).  Each addresses a specific concern.
	2.	Enhanced dispatcher collector – Modified generic.py to import the cache and define CFF_ENTRY_OPCODES.  The GenericDispatcherCollector now takes a cache instance, a skip flag and integrates heuristics and negative caching.  GenericDispatcherBlockInfo uses _DEF_USE_CACHE to reuse def/use lists.
	3.	High‑level pipeline – Created MicrocodeUnflattenPipeline that coordinates hashing, caching, dispatcher analysis, patching, snapshotting and Merkle diffing.  The pipeline exposes methods to process single functions or multiple functions in parallel and ensures the cache is closed properly.
	4.	Tests – Added unit tests under tests/unit/optimizers/microcode/flow/flattening/ to verify block hashing, def/use caching, persistence of dispatcher info and Merkle tree behaviour.  Because IDA APIs are not available, tests rely on dummy micro‑code classes and stubbed functions.

High‑Level Test Plan

Testing micro‑code analysis and caching in a repository without IDA requires isolating core logic and using dummy objects.  Below is a high‑level plan for verifying each major feature:
	1.	Block and function hashing
	•	Test: Create dummy block classes with deterministic opcode lists and compute their hashes using compute_block_hash().  Verify that identical blocks yield identical hashes and that a one‑byte change produces a different hash.  For compute_function_hash(), build an array of dummy blocks; verify that the function hash equals the hash of their concatenated block hashes.  Use a known test case to confirm the Merkle root matches expectations.
	•	Goal: Ensure stable fingerprints across sessions and catch changes when they occur.
	2.	Cache storage and lookup
	•	Test: Instantiate PersistentMicrocodeCache with an in‑memory SQLite database (:memory:).  Insert a dispatcher info structure for a block hash and a skip sentinel for another.  Close and reopen the cache; confirm that both entries can be retrieved intact.  Attempt to retrieve an unknown hash and verify that None is returned.  Test that the function processed marker and Merkle tree can be stored and retrieved.
	•	Goal: Validate that caching persists data correctly across sessions and that negative caching works.
	3.	Selective scanning
	•	Test: Create dummy micro‑code blocks, some containing opcodes from CFF_ENTRY_OPCODES and others without.  Mock GenericDispatcherCollector.visit_minsn() to record whether it reached the deeper analysis.  Run the collector on each block; verify that blocks lacking candidate opcodes are marked in the cache and not deeply analysed, while those with candidate opcodes are analysed normally.  Ensure that the skip sentinel prevents re‑analysis on subsequent runs.
	•	Goal: Demonstrate that the heuristic filters non‑dispatchers quickly and that the negative cache short‑circuits future scans.
	4.	Def/Use memoisation
	•	Test: Use a dummy InstructionDefUseCollector that counts how many times it is invoked.  Hash two identical blocks and run GenericDispatcherBlockInfo.parse() on each.  Assert that the collector is called only once; the second call should retrieve the lists from _DEF_USE_CACHE.  Change the block's opcode list and verify that the collector runs again.
	•	Goal: Ensure that def/use lists are reused across blocks with identical micro‑code.
	5.	Parallel processing
	•	Test: Create a list of dummy mba_t objects with varying numbers of blocks.  Instrument process_function() to record the order and timing of calls.  Invoke process_functions_in_parallel() with max_workers=2 and assert that two functions are processed concurrently by comparing timestamps.  Repeat with max_workers=1 and verify sequential execution.  Ensure that the cache is thread‑safe and free from race conditions by analysing logs or using thread locks.
	•	Goal: Confirm that the pipeline supports multi‑threaded processing and yields performance gains without data corruption.
	6.	Merkle tree diffing
	•	Test: Build a Merkle tree for a list of hashes using MerkleTree.build(); serialise and deserialise it.  Modify one leaf hash and rebuild; verify that the root hash changes and that merkle.diff() identifies the differing leaf index.  Store the original root in the cache, then call process_function() on a dummy function; assert that it skips processing when the root matches and performs processing when the root differs.
	•	Goal: Ensure the tree accurately reflects differences and that the pipeline uses the cached root to skip unchanged functions.
	7.	Patch recording and application
	•	Test: Simulate dispatcher analysis that returns a list of exit blocks.  Use PatchRecorder to record a "replace" action for the dispatch block with a jump to the first case.  Store the patch list in the cache.  Retrieve it and pass to BinaryPatcher (which will be stubbed in tests) to confirm that each action is dispatched to the correct method.  In a full IDA environment, verify that applying the patch changes the micro‑code or binary as expected.
	•	Goal: Validate that patch actions are recorded correctly and can be reapplied later.
	8.	Ctree snapshotting
	•	Test: Mock a cfunc_t‑like object with an AST structure that can be serialised into JSON.  Call save_ctree_snapshot() to store the snapshot in the cache.  Later, call load_ctree_snapshot() and verify that the restored object matches the original.  For environments without IDA, ensure that the fallback repr serialisation is used.
	•	Goal: Ensure decompiled output can be persisted and reused.

Intended Focus

The principal aim of this work was not to fully solve control‑flow flattening but to demonstrate an architecture for accelerating and persisting micro‑code analysis.  We emphasised clear separations of concern (hashing, caching, heuristics, patching, snapshotting) and modularity so that each component can evolve independently.  While some features (e.g., binary patching and ctree restoration) remain stubs without IDA, the plan shows how they would integrate into the pipeline.  The overarching focus is on performance and reproducibility: by skipping redundant work, running tasks concurrently and saving results, the plugin becomes more practical for real‑world binaries and large codebases.

Next Steps

To fully realise this vision, future work could:
	1.	Integrate with IDA APIs – Replace stubs in BinaryPatcher and ctree_snapshot with real calls to IDA's patching and decompilation functions, ensuring that changes are committed correctly.
	2.	Expand heuristics – Add pattern matching for additional flattening schemes or compiler patterns to further reduce emulation time.
	3.	Refine diff granularity – Use the Merkle tree to selectively re‑analyse only changed blocks rather than skipping or reprocessing entire functions.
	4.	Enhance parallelism – Explore process‑based parallelism to avoid Python's GIL and test on large real binaries to quantify speed‑ups.

⸻

## Hodur-Style State Machine Unflattening (2025)

### Overview

Hodur malware uses a distinct control flow flattening pattern that differs from O-LLVM:

| Feature | O-LLVM | Hodur |
|---------|--------|-------|
| Dispatcher | Single `switch` block with `m_jtbl` | Nested `while(1)` loops |
| Comparison | `switch(var)` → jump table | `jnz var, CONST` / `jz var, CONST` |
| Structure | Flat switch-case | 10+ levels of nested while loops |
| State var | Usually register | Usually stack variable (`mop_S`) |

### Problem: Cascading Unreachability

The existing `FixPredecessorOfConditionalJumpBlock` rule was designed for O-LLVM and caused **cascading unreachability** on Hodur functions:

1. Small "entry blocks" (API result checks, loop conditions) were redirected
2. Entry blocks lead INTO the state machine dispatcher
3. When redirected, dispatcher becomes unreachable
4. Entire state machine removed → 196 lines → 7 lines

**Fix Applied**: Added dispatcher detection heuristic (if ≥90% of predecessors go same direction → skip block). Updated `example_hodur.json` to disable problematic rule.

### State Variable Detection Algorithms

Eight algorithms for detecting state variables, ordered by complexity:

#### Algorithm 1: Pattern Matching (Static)
```python
def pattern_matching_detection(mba):
    """Look for: mov LARGE_CONST, var in early blocks (0-5)"""
    candidates = []
    for blk_idx in range(min(mba.qty, 5)):
        for ins in iterate_insns(blk_idx):
            if ins.opcode == m_mov and ins.l.t == mop_n:
                if ins.l.nnn.value > 0x10000:
                    candidates.append({'var': ins.d, 'init_value': ins.l.nnn.value})
    # Verify var appears in comparisons
    return score_and_select(candidates)
```
**Pros**: Fast, simple | **Cons**: Misses obfuscated init, SSA issues

#### Algorithm 2: Dataflow Analysis (Reaching Definitions)
Track which definitions reach each use. Find variables with constant defs that flow to comparisons.
**Pros**: Handles SSA | **Cons**: Complex, slower

#### Algorithm 3: CFG Structure Analysis (Dominator-Based)
Find dispatcher block first (many predecessors + conditional jump), extract compared variable.
**Pros**: Works for both O-LLVM and Hodur | **Cons**: May miss low-pred dispatchers

#### Algorithm 4: Constant Propagation
Track variables receiving multiple distinct large constants.
```python
var_constants = defaultdict(set)
for blk in blocks:
    for ins in insns:
        if ins.opcode == m_mov and is_large_const(ins.l):
            var_constants[var_key(ins.d)].add(ins.l.nnn.value)
# State var has many unique constants
return max(var_constants, key=lambda v: len(var_constants[v]))
```
**Pros**: Simple, direct | **Cons**: May catch counters

#### Algorithm 5: Loop Analysis (Back-Edge Detection)
Find variables that control loop back-edges.
**Pros**: Semantically meaningful | **Cons**: Complex CFG analysis

#### Algorithm 6: Symbolic Execution
Execute symbolically, track variables determining branch directions.
**Pros**: Most accurate | **Cons**: Slow, path explosion

#### Algorithm 7: Frequency Analysis
```python
score = comparison_freq[var] * assignment_freq[var]
```
**Pros**: Fast | **Cons**: False positives with counters

#### Algorithm 8: Machine Learning
Train classifier on features: n_const_assignments, n_comparisons, const_entropy, etc.
**Pros**: Learns complex patterns | **Cons**: Needs training data

### Recommended Hybrid Approach

```python
def hybrid_detection(mba):
    # Stage 1: Fast CFG structure check
    dispatcher = find_dispatcher_by_predecessor_count(mba)
    if dispatcher:
        candidate = extract_var_from_dispatcher(dispatcher)
        if verify_candidate(candidate): return candidate

    # Stage 2: Constant propagation for candidates
    candidates = constant_propagation_detection(mba)

    # Stage 3: Score with frequency analysis
    for c in candidates:
        c['score'] = frequency_score(mba, c['var'])

    # Stage 4: Verify with dataflow
    best = max(candidates, key=lambda c: c['score'])
    if verify_with_dataflow(mba, best): return best

    # Stage 5: Fall back to symbolic (expensive)
    return symbolic_execution_detection(mba)
```

### Scoring Function

```python
def score_candidate(c):
    score = len(c['comparisons']) * 10
    score += len(c['assignments']) * 5

    # Bonus for overlap between compared and assigned values
    cmp_vals = {x['value'] for x in c['comparisons']}
    asgn_vals = {x['value'] for x in c['assignments']}
    score += len(cmp_vals & asgn_vals) * 20

    # Bonus if init value is compared
    if c['init_value'] in cmp_vals:
        score += 50

    # Minimum thresholds
    if len(c['comparisons']) < 3 or len(c['assignments']) < 3:
        return 0
    return score
```

### CFG Transformation Algorithm

Once state variable and handlers are detected:

```
BEFORE (State Machine):              AFTER (Unflattened):
┌─────────┐                         ┌─────────┐
│ State 1 │──┐                      │ State 1 │
│ v17=S2  │  │                      └────┬────┘
└─────────┘  │                           │
             ▼                           ▼
┌─────────────────┐                 ┌─────────┐
│   Dispatcher    │        →        │ State 2 │
│ while(v17==...) │                 └────┬────┘
└─────────────────┘                      │
             ▲                           ▼
┌─────────┐  │                      ┌─────────┐
│ State 2 │──┘                      │ State 3 │
│ v17=S3  │                         └─────────┘
└─────────┘
```

**Algorithm**:
1. Build execution order (topological sort from init state)
2. For each state transition, redirect CFG edge directly to next handler
3. Handle conditional transitions (keep branches, redirect targets)
4. Remove unreachable dispatcher blocks
5. Verify with `safe_verify(mba)`

### Issue Tracking

| Issue ID | Title | Status |
|----------|-------|--------|
| d810-ng-5wu | Fix: FixPredecessorOfConditionalJumpBlock cascading unreachability | ✅ CLOSED |
| d810-ng-gbj | Implement HodurUnflattener state variable detection | OPEN |
| d810-ng-iid | Implement HodurUnflattener CFG transformation | OPEN |

### Files

- `src/d810/optimizers/microcode/flow/flattening/unflattener_hodur.py` - Hodur unflattener
- `src/d810/optimizers/microcode/flow/flattening/fix_pred_cond_jump_block.py` - Fixed with dispatcher heuristic
- `src/d810/conf/example_hodur.json` - Config for Hodur-style functions
- `tests/system/test_libdeobfuscated.py::test_hodur_func` - Integration test

### Success Criteria

1. **Detection**: State variable correctly identified with all states
2. **Extraction**: All state handlers and transitions mapped
3. **Transformation**: CFG correctly rewritten
4. **Output**: ~50 lines (down from 196), clean sequential code
5. **Semantics**: All API calls preserved, same execution order

⸻
