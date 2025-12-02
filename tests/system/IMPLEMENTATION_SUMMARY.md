# Test Capture System - Implementation Summary

## Overview

A comprehensive SQLite-based test result capture system for comparing deobfuscation outputs across test runs and test suites.

## Files Created

### 1. `/tests/system/test_capture.py` (779 lines)

Main implementation module containing:

- **Database Schema**
  - `test_results` table with comprehensive fields
  - Views: `latest_results`, `function_coverage`
  - Indices for fast queries
  - Schema versioning support

- **TestResultCapture** class
  - Context manager for capturing test results
  - Stores: test metadata, code before/after, statistics, rules fired, pass/fail status
  - Automatic JSON serialization of complex fields

- **TestResultQuery** class
  - `list_functions()` - All functions with coverage info
  - `get_function_results(name)` - All results for a function
  - `compare_suites(suite1, suite2)` - Diff between test suites
  - `get_test_suites()` - List all test suites
  - `get_recent_runs(limit)` - Recent test runs
  - `get_stats_summary()` - Database statistics

- **Pytest Plugin (CapturePlugin)**
  - Automatic capture via `pytest_runtest_logreport` hook
  - Triggered by `--capture-to-db` flag
  - Reads test data from `request.user_properties`

- **CLI Interface**
  - `python -m tests.system.test_capture <command>`
  - Commands: list-functions, get-function, compare-suites, list-suites, recent, stats
  - Rich formatted output for terminal

### 2. `/tests/system/test_capture_integration.py` (283 lines)

Comprehensive integration tests:
- `test_database_initialization` - Schema creation
- `test_capture_result` - Basic capture
- `test_query_functions` - Function listing with coverage
- `test_get_function_results` - Result retrieval and ordering
- `test_compare_suites` - Suite comparison logic
- `test_recent_runs` - Recent run queries
- `test_stats_summary` - Statistics aggregation
- `test_get_test_suites` - Suite listing

All tests pass ✓

### 3. `/tests/system/TEST_CAPTURE_README.md` (489 lines)

Comprehensive user documentation:
- Quick start guide
- Database schema documentation
- CLI command reference with examples
- Manual capture API examples
- DSL test integration guide
- Use cases and workflows
- Advanced SQL queries
- Troubleshooting guide

### 4. `/tests/system/example_capture_usage.py` (220 lines)

Working examples demonstrating:
- Manual capture with TestResultCapture
- Pytest integration usage
- Test code integration patterns
- Common use cases with CLI commands

### 5. Updated `/tests/system/conftest.py`

Added:
- `--capture-to-db` pytest option
- `pytest_configure` hook to register CapturePlugin
- `db_capture` fixture for manual capture in tests

### 6. Updated `/src/d810/testing/runner.py`

Modified `run_deobfuscation_test()`:
- Added `db_capture` parameter
- Calls `db_capture.record()` on test success
- Passes function metadata to database

### 7. Updated `/.gitignore`

Added:
- `tests/system/.test_results.db` to ignore database file

## Database Schema

```sql
CREATE TABLE test_results (
    id INTEGER PRIMARY KEY AUTOINCREMENT,

    -- Test identification
    test_suite TEXT NOT NULL,
    test_name TEXT NOT NULL,
    test_class TEXT,
    test_file TEXT,

    -- Function identification
    function_name TEXT NOT NULL,
    binary_name TEXT,
    function_address TEXT,

    -- Deobfuscation results
    code_before TEXT,
    code_after TEXT,
    code_changed BOOLEAN,

    -- Statistics (JSON)
    rules_fired TEXT,           -- JSON list
    stats_dict TEXT,            -- JSON object
    optimizer_usage TEXT,       -- JSON object
    cfg_rule_usage TEXT,        -- JSON object

    -- Test outcome
    passed BOOLEAN NOT NULL,
    error_message TEXT,
    skipped BOOLEAN DEFAULT 0,
    skip_reason TEXT,

    -- Metadata
    timestamp DATETIME DEFAULT CURRENT_TIMESTAMP,
    test_duration REAL,
    pytest_nodeid TEXT
);
```

## Usage Examples

### Capture Test Results

```bash
# Run tests with capture
pytest tests/system/test_libdeobfuscated.py --capture-to-db -v
pytest tests/system/test_libdeobfuscated_dsl.py --capture-to-db -v
```

### Query Results

```bash
# List all functions tested
python -m tests.system.test_capture list-functions

# Get results for specific function
python -m tests.system.test_capture get-function test_chained_add

# Compare two test suites
python -m tests.system.test_capture compare-suites \
    test_libdeobfuscated.py \
    test_libdeobfuscated_dsl.py

# Show recent runs
python -m tests.system.test_capture recent --limit 10

# Database statistics
python -m tests.system.test_capture stats
```

### Manual Capture in Tests

```python
def test_my_function(self, d810_state, db_capture, pseudocode_to_string):
    """Test with manual capture."""
    func_ea = get_func_ea("my_function")

    with d810_state() as state:
        # Decompile before/after
        state.stop_d810()
        code_before = pseudocode_to_string(
            idaapi.decompile(func_ea).get_pseudocode()
        )

        state.start_d810()
        code_after = pseudocode_to_string(
            idaapi.decompile(func_ea).get_pseudocode()
        )

        # Capture result
        db_capture.record(
            function_name="my_function",
            code_before=code_before,
            code_after=code_after,
            stats=state.stats,
            passed=True,
            function_address=hex(func_ea),
        )
```

### Automatic Capture with DSL Tests

```python
@pytest.mark.parametrize("case", TEST_CASES, ids=lambda c: c.test_id)
def test_deobfuscation(
    self,
    case,
    d810_state,
    pseudocode_to_string,
    code_comparator,
    db_capture,  # Add this
):
    """Test with automatic capture."""
    run_deobfuscation_test(
        case=case,
        d810_state=d810_state,
        pseudocode_to_string=pseudocode_to_string,
        code_comparator=code_comparator,
        db_capture=db_capture,  # Pass to runner
    )
```

## Key Features

1. **Comprehensive Capture**
   - Test metadata (suite, name, class, file)
   - Function details (name, binary, address)
   - Code before/after deobfuscation
   - Full statistics dictionary
   - Rules fired and optimizer usage
   - Test outcome (pass/fail/skip)
   - Timing information

2. **Flexible Querying**
   - List all functions with coverage stats
   - Get all results for specific function
   - Compare results between test suites
   - Find differences in code/rules
   - Track recent runs
   - Database-wide statistics

3. **Suite Comparison**
   - Functions tested by both suites
   - Functions unique to each suite
   - Code differences for common functions
   - Rule usage differences
   - Pass/fail status comparison

4. **Multiple Integration Modes**
   - Automatic via pytest plugin
   - Manual via `db_capture` fixture
   - Automatic with DSL test runner
   - Programmatic via Python API

5. **CLI Tool**
   - Rich terminal output
   - Multiple query commands
   - Filtering and limiting
   - Human-readable formatting

## Use Cases

### 1. Track Regression

```bash
# Capture baseline
pytest tests/system/test_*.py --capture-to-db

# Make code changes...

# Run again
pytest tests/system/test_*.py --capture-to-db

# Compare
python -m tests.system.test_capture get-function test_chained_add --limit 5
```

### 2. Compare Implementation Approaches

```bash
# Capture from both suites
pytest tests/system/test_libdeobfuscated.py --capture-to-db
pytest tests/system/test_libdeobfuscated_dsl.py --capture-to-db

# Compare
python -m tests.system.test_capture compare-suites \
    test_libdeobfuscated.py \
    test_libdeobfuscated_dsl.py \
    --show-code
```

### 3. Identify Coverage Gaps

```bash
# List functions
python -m tests.system.test_capture list-functions

# Find functions tested by only one suite
python -m tests.system.test_capture list-functions | grep "1      "
```

### 4. Rule Usage Analysis

```bash
# See which rules fired
python -m tests.system.test_capture get-function test_xor

# Direct SQL for aggregation
sqlite3 tests/system/.test_results.db <<SQL
SELECT json_each.value as rule, COUNT(*) as count
FROM test_results, json_each(test_results.rules_fired)
GROUP BY rule
ORDER BY count DESC;
SQL
```

## Testing

All integration tests pass:

```
tests/system/test_capture_integration.py::test_database_initialization PASSED
tests/system/test_capture_integration.py::test_capture_result PASSED
tests/system/test_capture_integration.py::test_query_functions PASSED
tests/system/test_capture_integration.py::test_get_function_results PASSED
tests/system/test_capture_integration.py::test_compare_suites PASSED
tests/system/test_capture_integration.py::test_recent_runs PASSED
tests/system/test_capture_integration.py::test_stats_summary PASSED
tests/system/test_capture_integration.py::test_get_test_suites PASSED

8 passed in 0.11s
```

## Database Location

- Path: `tests/system/.test_results.db`
- Git-ignored by default
- Created automatically on first capture
- Schema version: 1 (supports migrations)

## Advanced Queries

Direct SQLiteaccess:

```bash
sqlite3 tests/system/.test_results.db
```

Example queries:

```sql
-- Find failing tests
SELECT function_name, test_suite, error_message
FROM test_results
WHERE passed = 0
ORDER BY timestamp DESC;

-- Most commonly fired rules
SELECT json_each.value as rule_name, COUNT(*) as count
FROM test_results, json_each(test_results.rules_fired)
GROUP BY rule_name
ORDER BY count DESC;

-- Code changes over time
SELECT function_name, timestamp, code_changed
FROM test_results
WHERE function_name = 'test_chained_add'
ORDER BY timestamp DESC;

-- Compare rule usage between suites
SELECT
    t1.function_name,
    json_array_length(t1.rules_fired) as rules_suite1,
    json_array_length(t2.rules_fired) as rules_suite2
FROM
    (SELECT * FROM latest_results WHERE test_suite = 'test_libdeobfuscated.py') t1
JOIN
    (SELECT * FROM latest_results WHERE test_suite = 'test_libdeobfuscated_dsl.py') t2
ON t1.function_name = t2.function_name;
```

## Implementation Notes

1. **Schema Design**
   - JSON fields for complex nested data
   - Views for common queries
   - Indices for performance
   - No UNIQUE constraints (allows multiple runs)

2. **Timestamp Granularity**
   - SQLite DATETIME has second-level precision
   - Multiple inserts in same second are allowed
   - Ordering by timestamp DESC, then ID works correctly

3. **Pytest Integration**
   - Plugin registers via `pytest_configure`
   - Data passed via `request.user_properties`
   - Hooks in `pytest_runtest_logreport` (call phase)

4. **Error Handling**
   - Capture errors don't break tests
   - Missing data handled gracefully
   - Optional parameters throughout

5. **Class Naming**
   - `TestResultCapture` and `TestResultQuery` trigger pytest warnings
   - This is expected and harmless (they're not test classes)
   - Could rename to avoid warnings if desired

## Future Enhancements

Potential additions:

1. **Schema Migrations**
   - Migration framework using schema_version
   - Automatic upgrades on database open

2. **Web Dashboard**
   - Flask/FastAPI app for browsing results
   - Charts and visualizations
   - Interactive comparisons

3. **Regression Detection**
   - Automatic detection of performance regressions
   - Alert when rules stop firing
   - Code quality metrics

4. **Export Formats**
   - JSON export for external tools
   - HTML report generation
   - Markdown summaries

5. **Integration with CI**
   - Automatic capture in GitHub Actions
   - Store results as artifacts
   - Compare PR results to baseline

## Conclusion

The test capture system provides a comprehensive solution for:
- Tracking test results over time
- Comparing deobfuscation outputs
- Analyzing rule usage
- Identifying coverage gaps
- Regression detection

All requirements met:
✓ SQLite database with comprehensive schema
✓ Automatic capture via pytest plugin
✓ CLI for querying and comparison
✓ Manual capture API
✓ DSL test integration
✓ Suite comparison
✓ Function coverage tracking
✓ Comprehensive documentation
✓ Working examples
✓ Integration tests
