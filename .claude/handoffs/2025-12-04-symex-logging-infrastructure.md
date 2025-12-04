# Symbolic Execution Investigation - Logging Infrastructure Complete

## 1. Primary Request and Intent

The user's primary goal is to fix the `UnflattenerFakeJump` regression for OR-based state machine patterns like `abc_f6_or_dispatch`. The investigation revealed:

1. **The bug**: UnflattenerFakeJump produces wrong output (`return 0xFFFFFFFFLL` instead of `return a1 | 0xFFu`)
2. **Root cause identified**: d810-ng introduced a "safety check" that uses `continue` (partial processing) instead of `return 0` (abort all) when unresolved histories exist
3. **Key insight**: MopTracker is path-insensitive and finds spurious paths that give inconsistent resolved values

Before making a fix decision, the user wants to:
- Create proper beads to track work
- Build structured logging infrastructure (SQLite) to avoid burning Hub context
- Run actual investigation with debug_scope to capture real MopTracker output
- Determine if resolved values are consistent or inconsistent

## 2. Key Technical Concepts

- **MopTracker**: Backward data-flow analysis (backward slicing), NOT path finding
- **MopHistory**: One possible execution path with instructions that define a variable's value
- **Unresolved history**: Path where tracker couldn't determine constant value (loops, calls, limits) - NOT invalid
- **Flattening Invariant**: "All paths through a predecessor have same state value" - holds in real execution but MopTracker doesn't respect it
- **Spurious paths**: Path-insensitive search explores impossible paths that violate dispatcher routing
- **debug_scope**: Context manager for temporary DEBUG logging to SQLite
- **log-analyst agent**: Builds targeted SQL queries to extract insights without dumping raw logs

## 3. Files and Code Sections

### `.beads/issues.jsonl`
- **Why important**: Contains all work items tracked via beads system
- **Changes made**: Added 7 new beads:
  - `d810ng-symex` (EPIC: Symbolic Execution Architecture)
  - `d810ng-symex-01` (Investigation)
  - `d810ng-symex-02` (Decision)
  - `d810ng-slog` (EPIC: Structured SQLite Logging)
  - `d810ng-slog-01` (SQLite handler)
  - `d810ng-slog-02` (Context manager)
  - `d810ng-slog-03` (Pytest fixture)

### `.claude/knowledge/moptracker_symbolic_execution.md`
- **Why important**: Comprehensive knowledge doc capturing all investigation findings
- **Changes made**: Created with sections on MopTracker, unresolved histories, infrastructure, and structured logging

### `src/d810/core/structured_logging.py`
- **Why important**: SQLite logging handler enabling agent-friendly debug analysis
- **Changes made**: Created with SQLiteHandler, debug_scope, query_logs
- **Key code**:
```python
@contextmanager
def debug_scope(
    loggers: Union[List[str], str] = 'd810',
    db_path: str = '.d810_debug.db',
    test_id: str = None,
    level: int = logging.DEBUG
):
    """Context manager that temporarily enables DEBUG logging to SQLite."""
    ...
```

### `.claude/agents/log-analyst.md`
- **Why important**: Agent definition for SQL query building and log summarization
- **Changes made**: Created with query patterns, workflow, and output format
- **Key patterns**:
```sql
-- Find history values
SELECT json_extract(extra, '$.value') as value,
       json_extract(extra, '$.resolved') as resolved
FROM logs
WHERE logger LIKE 'd810.hexrays.tracker%'
AND test_id = ?
AND message LIKE 'History%'
ORDER BY id;

-- Check consistency
SELECT COUNT(DISTINCT json_extract(extra, '$.value')) as unique_values
FROM logs WHERE json_extract(extra, '$.resolved') = 1;
```

### `.claude/agents/researcher.md`
- **Why important**: Updated to use log-analyst workflow
- **Changes made**: Added LOG ANALYSIS section explaining how to use debug_scope and delegate to log-analyst

### `tests/unit/core/test_log_analyst_integration.py`
- **Why important**: Integration test with sample MopTracker data for workflow verification
- **Changes made**: Created with test database and SQL query verification

## 4. Problem Solving

### Solved
1. **Root cause identified**: d810-ng's safety check uses `continue` instead of `return 0`
2. **MopTracker understood**: Backward data-flow analysis, unresolved = incomplete (not invalid)
3. **Invariant clarified**: Holds in real execution, MopTracker is path-insensitive
4. **Logging infrastructure built**: SQLite handler, debug_scope, log-analyst agent
5. **Workflow verified**: Tested log-analyst pattern with sample data - works correctly

### Ongoing
1. **Investigation pending**: Need to run actual test with debug_scope
2. **Decision pending**: Which fix approach (Options A-D)

## 5. Pending Tasks

Beads to complete:

| Bead ID | Title | Status |
|---------|-------|--------|
| d810ng-slog-01 | SQLite handler | Done (needs bead close) |
| d810ng-slog-02 | Context manager | Done (needs bead close) |
| d810ng-symex-01 | Investigation | Ready to execute |
| d810ng-symex-02 | Decision | Blocked by symex-01 |

## 6. Current Work

The logging infrastructure is complete. The workflow verified:

```
Hub → Researcher: "Investigate abc_f6_or_dispatch"
      ↓
Researcher: Runs test with debug_scope
      ↓
Researcher → Log-Analyst (via Explore): "Query DB - what values found?"
      ↓
Log-Analyst: Builds SQL, returns summary
      ↓
Researcher → Hub: Structured findings (not raw logs)
```

## 7. Next Step

**Execute d810ng-symex-01 investigation**:

1. Run `abc_f6_or_dispatch` test with `debug_scope`:
```python
from d810.core.structured_logging import debug_scope

with debug_scope(
    loggers=['d810.hexrays.tracker', 'd810.optimizers.microcode.flow.flattening'],
    db_path='/tmp/abc_f6_debug.db',
    test_id='test_abc_f6_or_dispatch'
):
    # Run deobfuscation test
    result = deobfuscate('abc_f6_or_dispatch')
```

2. Dispatch Explore agent with log-analyst prompt to analyze the logs
3. Answer: Are the resolved MopTracker history values consistent?
4. Update d810ng-symex-02 decision bead with findings

## Decision Options (for reference)

| Option | Effort | Description |
|--------|--------|-------------|
| A | Low | Consistency check - verify all resolved values agree |
| B | Medium | Constraint-aware MopTracker - prune invalid paths |
| C | High | SymbolicMicroCodeInterpreter - full forward symbolic |
| D | Low | Revert to d810 behavior - `return 0` instead of `continue` |

## Key Files Reference

| File | Purpose |
|------|---------|
| `src/d810/core/structured_logging.py` | SQLite logging infrastructure |
| `.claude/agents/log-analyst.md` | SQL query building agent |
| `.claude/knowledge/moptracker_symbolic_execution.md` | Investigation knowledge |
| `.beads/issues.jsonl` | Work tracking (symex, slog beads) |
| `src/d810/optimizers/microcode/flow/flattening/unflattener_fake_jump.py` | The failing rule |
| `src/d810/hexrays/tracker.py` | MopTracker implementation |
