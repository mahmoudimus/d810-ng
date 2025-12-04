# Run abc_f6_or_dispatch Test with Structured Logging

## 1. Primary Request and Intent

The user wants to:
1. **Run the actual `abc_f6_or_dispatch` test** in headless IDA Pro
2. **Capture debug logs to SQLite** using the `debug_scope` context manager
3. **Analyze the logs** to determine if resolved MopTracker history values are consistent
4. **Make a fix decision** for UnflattenerFakeJump based on real data

The test infrastructure and structured logging are complete - the blocker is actually executing the test.

## 2. Key Technical Concepts

- **MopTracker**: Backward data-flow analysis that traces variable lineage
- **MopHistory**: Represents one execution path with resolved/unresolved status
- **Unresolved history**: Incomplete data (dispatcher back-edges), NOT invalid paths
- **Spurious paths**: Path-insensitive search finds impossible paths with inconsistent values
- **debug_scope**: Context manager for temporary DEBUG logging to SQLite
- **Headless IDA**: Tests can run via `idapro` module/idalib (confirmed in Truth DB)
- **--dangerously-skip-permissions**: Flag that may be needed for subagent Bash access

## 3. Files and Code Sections

### `src/d810/core/structured_logging.py`
- **Why important**: SQLite logging infrastructure for capturing debug output
- **Status**: Complete and working
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
```

### `.claude/agents/log-analyst.md`
- **Why important**: Agent definition for querying SQLite logs
- **Status**: Complete
- **Key queries**:
```sql
-- Find history values
SELECT json_extract(extra, '$.value') as value,
       json_extract(extra, '$.resolved') as resolved
FROM logs WHERE logger LIKE 'd810.hexrays.tracker%'

-- Check consistency
SELECT COUNT(DISTINCT json_extract(extra, '$.value')) as unique_values
FROM logs WHERE json_extract(extra, '$.resolved') = 1;
```

### `tests/system/cases/libobfuscated_comprehensive.py` (line 279)
- **Why important**: Defines the test case
- **Test definition**:
```python
DeobfuscationCase(
    function="abc_f6_or_dispatch",
    description="ABC pattern with OR operations on state variables",
    project="example_libobfuscated_no_fixprecedessor.json",
    expected_code="""
        __int64 __fastcall abc_f6_or_dispatch(int a1)
        {
            return a1 | 0xFFu;
        }
    """,
    required_rules=["UnflattenerFakeJump"],
)
```

### `.beads/issues.jsonl`
- **Why important**: Tracks work items
- **Relevant beads**:
  - `d810ng-symex` - EPIC: Symbolic Execution Architecture
  - `d810ng-symex-01` - Investigation (IN PROGRESS)
  - `d810ng-symex-02` - Decision (BLOCKED)
  - `d810ng-slog-*` - Structured logging (COMPLETE)

## 4. Problem Solving

### Solved
- Root cause identified (d810-ng safety check uses `continue` vs `return 0`)
- MopTracker behavior understood (backward slicing, path-insensitive)
- Structured logging infrastructure built
- Log-analyst agent created

### Ongoing Blockers
1. **Air terminal tools not working**: Commands get "scheduled" but never execute
2. **Subagent Bash access**: Agents report no Bash access or time out
3. **Possible fix**: May need `--dangerously-skip-permissions` flag for subagents

## 5. Pending Tasks

1. **Run the actual test**:
   ```bash
   cd /Users/mahmoud/src/idapro/d810-ng
   PYTHONPATH=src python -m pytest tests/system/test_libdeobfuscated_dsl.py -k "abc_f6_or_dispatch" -v
   ```

2. **Capture logs with debug_scope** (may need to modify test or create wrapper)

3. **Query SQLite for MopTracker history values**

4. **Determine if resolved values are consistent**

5. **Update d810ng-symex-02 decision bead** with findings

## 6. Current Work

Attempting to execute the `abc_f6_or_dispatch` pytest but blocked by:
- Air terminal MCP tools timing out (commands scheduled but not executing)
- Subagents not having Bash access or timing out

Last attempted:
```bash
PYTHONPATH=src python -m pytest tests/system/test_libdeobfuscated_dsl.py -k "abc_f6_or_dispatch" -v
```

User asked about `--dangerously-skip-permissions` flag which may be needed.

## 7. Next Step

1. **Fix the execution issue**: Either:
   - Ensure subagents have Bash access (check `--dangerously-skip-permissions`)
   - Debug why Air terminal commands aren't executing
   - Or have user run the command directly

2. **Once test can run**: Wrap with debug_scope to capture logs:
   ```python
   from d810.core.structured_logging import debug_scope

   with debug_scope(
       loggers=['d810.hexrays.tracker', 'd810.optimizers.microcode.flow.flattening'],
       db_path='/tmp/abc_f6_debug.db',
       test_id='abc_f6_or_dispatch'
   ):
       # Run pytest programmatically or via subprocess
   ```

3. **Query the resulting SQLite database** for MopTracker history consistency

## Key Command to Run

```bash
cd /Users/mahmoud/src/idapro/d810-ng
PYTHONPATH=src python -m pytest tests/system/test_libdeobfuscated_dsl.py -k "abc_f6_or_dispatch" -v -s
```

## Truth DB Fact (for reference)

```
FACT: pytest supports headless_execution
Proof: The idapro module/idalib enables headless IDA Pro access. Documented in tests/README.md Option 1.
```

## Investigation Background

### The Bug
UnflattenerFakeJump produces wrong output for OR-based state machines:
- **Expected**: `return a1 | 0xFFu`
- **Actual**: `return 0xFFFFFFFFLL` with `++global_side_effect`

### Root Cause (from code analysis)
d810-ng introduced a "safety check" that uses `continue` (partial processing) instead of `return 0` (abort all) when unresolved histories exist. This causes partial CFG transformation.

### What We Need to Confirm
Are the resolved MopTracker history values consistent?
- If YES: Problem is downstream in CFG transformation
- If NO: Spurious paths are giving inconsistent values (confirms hypothesis)

### Expected Findings (based on earlier analysis)
- 5 histories total
- 3 resolved (values possibly: 0xF6951, 0xF6951, 0xF6953 - INCONSISTENT)
- 2 unresolved (dispatcher back-edges)

### Decision Options After Investigation

| Option | Effort | Description |
|--------|--------|-------------|
| A | Low | Consistency check - verify all resolved values agree |
| B | Medium | Constraint-aware MopTracker - prune invalid paths |
| C | High | SymbolicMicroCodeInterpreter - full forward symbolic |
| D | Low | Revert to d810 behavior - `return 0` instead of `continue` |

## Knowledge References

- `.claude/knowledge/moptracker_symbolic_execution.md` - Full investigation context
- `.claude/agents/log-analyst.md` - SQL query patterns for log analysis
- `docs/symbolic-microcode-plan.md` - SymbolicMicroCodeInterpreter design
