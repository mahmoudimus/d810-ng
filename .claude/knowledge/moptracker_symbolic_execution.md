# MopTracker & Symbolic Execution Architecture

## Overview

This document captures the findings from the December 2024 investigation into MopTracker, its relationship to symbolic execution, and the architectural decisions facing d810-ng for control flow unflattening.

---

## 1. MopTracker: What It Actually Does

### Core Purpose

**MopTracker performs backward data-flow analysis (backward slicing)** to trace variable lineage through execution paths.

### Input/Output

| Aspect | Description |
|--------|-------------|
| **Input** | A variable (`mop_t`) to track, starting block, optional limits |
| **Output** | List of `MopHistory` objects - one per traced path |

### What is MopHistory?

A `MopHistory` represents **one possible execution path** with the sequence of instructions that define the tracked variable's value:

- `block_path`: Ordered list of blocks traversed (backward)
- `ins_list`: Instructions within each block that affect the tracked variable
- Embedded `MicroCodeInterpreter` that can replay the path to compute final values
- `is_resolved()`: Returns true if all dependencies have known constant values

### Algorithm Summary

1. Start from given block/instruction with variables to track (`_unresolved_mops`)
2. Walk backward through instructions, looking for definitions of tracked variables
3. When a definition is found:
   - Remove the defined variable from `_unresolved_mops`
   - Add any variables used in that definition to `_unresolved_mops`
4. Continue until:
   - All variables are resolved (have constant values), OR
   - Hit a block with multiple predecessors (fork point), OR
   - Reach max depth/path limits
5. At fork points: Clone the tracker and recursively explore each predecessor
6. Return all discovered paths as MopHistory objects

### Key Methods

| Method | Purpose |
|--------|---------|
| `search_backward()` | Main entry - orchestrates backward search, handles forking |
| `search_until_multiple_predecessor()` | Linear backward walk until hitting a fork point |
| `blk_find_def_backward()` | Find definitions of tracked variables within a block |
| `MopHistory.is_resolved()` | Check if all tracked variables have known values |
| `MopHistory.get_mop_constant_value()` | Execute the path to compute a variable's final value |

---

## 2. What "Unresolved" Means

### Definition

A `MopHistory` is **unresolved** when the tracker couldn't determine a constant value for the tracked variable along that path.

### Causes of Unresolved Histories

| Cause | Description |
|-------|-------------|
| **Dispatcher back-edge** | Path loops back to dispatcher before finding constant |
| **Max block limit** | `max_nb_block` exceeded |
| **Max path limit** | `max_path` global limit exceeded |
| **Call instruction** | External call might modify state |
| **Entry block reached** | Variable comes from function arguments |

### Critical Insight

**Unresolved ≠ Invalid Path**

Unresolved histories are **valid execution paths with incomplete data**. The tracker just couldn't determine the final value.

In flattened control flow, **dispatcher back-edges are expected and normal**. They represent the loop structure of the state machine.

---

## 3. The OR-Based State Machine Problem

### The Pattern (abc_f6_or_dispatch)

```c
int abc_f6_or_dispatch(int input) {
    unsigned int state = 1010000;
    int result = input;
    while (1) {
        switch (state) {
        case 1010000:
            result = result | 0xF0;
            state = state | 1;  // Cumulative OR
            break;
        case 1010001:
            result = result | 0x0F;
            state = state | 2;  // Cumulative OR
            break;
        case 1010003:
            return result;
        }
    }
}
```

### Standard vs OR-Based Flattening

| Type | State Update | MopTracker Behavior |
|------|--------------|---------------------|
| **Standard** | `state = CONST` | Easy - finds constant directly |
| **OR-based** | `state = state \| CONST` | Must trace prior value first |

### The Flattening Invariant

> "All execution paths through a specific predecessor block have the same state variable value at the conditional jump."

**For standard flattening**: Clearly holds - each case sets state to a constant.

**For OR-based flattening**: Also holds in **real execution** because dispatcher routing is deterministic. But MopTracker's path-insensitive backward search may find **spurious paths** that violate it.

### Current MopTracker Results for abc_f6_or_dispatch

```
5 histories from predecessor Block 2:
├── 3 resolved (found constant values)
│   └── Some may have INCONSISTENT values (spurious paths)
└── 2 unresolved (dispatcher back-edges)
```

---

## 4. Existing Infrastructure

### MicroCodeInterpreter (`src/d810/expr/emulator.py`)

Forward concrete execution of microcode:
- Executes instructions sequentially
- Updates environment (register/memory state)
- Has `symbolic_mode` flag (fabricates synthetic values for unknowns)
- Does NOT track path constraints

### z3_utils.py (`src/d810/expr/z3_utils.py`)

IDA-specific Z3 utilities:
- `ast_to_z3_expression()`: Converts AstNode → Z3 BitVec
- Supports most microcode opcodes (arithmetic, bitwise, comparisons)
- Used for runtime verification during deobfuscation

### Two Z3 Modules

| Module | Purpose | Input |
|--------|---------|-------|
| `d810.mba.backends.z3` | Rule verification (pure, no IDA) | `SymbolicExpression` |
| `d810.expr.z3_utils` | Runtime verification (IDA-specific) | `AstNode` |

---

## 5. SymbolicMicroCodeInterpreter Proposal

### Concept

Enhance `MicroCodeInterpreter` to use Z3 BitVecs for **forward symbolic execution** with path constraint tracking.

### Why Forward Instead of Backward?

| Approach | Pros | Cons |
|----------|------|------|
| **Backward (MopTracker)** | Efficient for simple cases | Path-insensitive, finds spurious paths |
| **Forward (Symbolic)** | Path-sensitive, respects dispatcher routing | Potential path explosion |

### Design (from `docs/symbolic-microcode-plan.md`)

1. Keep concrete `MicroCodeInterpreter` as fast path
2. Add `SymbolicMicroCodeInterpreter` with same API:
   - Operations produce Z3 BitVecs instead of Python ints
   - Track path constraints at conditional branches
   - Use Z3 solver for feasibility checking
3. Use as fallback when concrete execution fails

### Why NOT Triton/Unicorn?

| Tool | Problem |
|------|---------|
| Triton | Works on native x86, not microcode |
| Unicorn | CPU emulator, no symbolic support |
| Capstone | Disassembler only |

**The semantic gap**: d810 operates at microcode level. Native tools don't help.

---

## 6. Open Questions

### Q1: Why does filtering unresolved histories work for some patterns but not OR-based?

Hypothesis: The resolved histories have **inconsistent values** due to spurious paths, but the filtering heuristic doesn't check for consistency.

### Q2: Is the Flattening Invariant actually violated, or is MopTracker just path-insensitive?

The invariant holds in real execution. MopTracker's backward search explores paths that can't actually execute.

### Q3: Do we need full symbolic execution, or just constraint-aware filtering?

Options:
1. **Lightweight**: Check consistency of resolved values
2. **Medium**: Add constraint tracking to MicroCodeInterpreter
3. **Full**: Implement SymbolicMicroCodeInterpreter

### Q4: What exactly goes wrong downstream for abc_f6_or_dispatch?

The rule fires, patches are made, but output is wrong. Is the issue in:
- MopTracker's value resolution?
- The filtering heuristic?
- The CFG transformation itself?

---

## 7. Files Reference

| File | Purpose |
|------|---------|
| `src/d810/hexrays/tracker.py` | MopTracker implementation |
| `src/d810/expr/emulator.py` | MicroCodeInterpreter |
| `src/d810/expr/z3_utils.py` | IDA-specific Z3 utilities |
| `src/d810/mba/backends/z3.py` | Pure Z3 verification |
| `src/d810/optimizers/microcode/flow/flattening/unflattener_fake_jump.py` | The failing rule |
| `docs/symbolic-microcode-plan.md` | SymbolicMicroCodeInterpreter design |
| `samples/src/c/abc_f6_constants.c` | Test case source |

---

## 8. Structured Logging for Investigation

### Overview

d810-ng has a structured logging system that writes to SQLite instead of log files. This enables agents to query debug logs without burning context tokens.

### Components

| Component | Location | Purpose |
|-----------|----------|---------|
| `SQLiteHandler` | `src/d810/core/structured_logging.py` | Logging handler that writes to SQLite |
| `debug_scope` | `src/d810/core/structured_logging.py` | Context manager for temporary DEBUG logging |
| `query_logs` | `src/d810/core/structured_logging.py` | Helper to query logs with filters |
| `log-analyst` | `.claude/agents/log-analyst.md` | Agent for building SQL queries and summarizing findings |

### Usage Pattern

```python
from d810.core.structured_logging import debug_scope

# Capture logs during test
with debug_scope(
    loggers=['d810.hexrays.tracker'],
    db_path='/tmp/debug.db',
    test_id='test_abc_f6_or_dispatch'
):
    result = deobfuscate(func)

# Delegate analysis to log-analyst agent (preserves Hub context)
# Agent returns: "5 histories found: 3 resolved (0xF6951, 0xF6951, 0xF6953), 2 unresolved"
```

### Agent Workflow

```
Hub → Researcher: "Investigate abc_f6_or_dispatch"
      ↓
Researcher: Runs test with debug_scope
      ↓
Researcher → Log-Analyst: "Query /tmp/debug.db - what values found?"
      ↓
Log-Analyst: Builds SQL, returns summary
      ↓
Researcher → Hub: Structured findings (not raw logs)
```

### Database Schema

```sql
CREATE TABLE logs (
    id INTEGER PRIMARY KEY,
    timestamp TEXT,
    logger TEXT,       -- e.g., 'd810.hexrays.tracker'
    level TEXT,        -- DEBUG, INFO, WARNING, ERROR
    function TEXT,
    lineno INTEGER,
    message TEXT,
    extra JSON,        -- Structured data (histories, values)
    test_id TEXT       -- Correlate with test run
);
```
