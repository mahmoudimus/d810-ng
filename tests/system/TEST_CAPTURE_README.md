# Test Result Capture System

This directory contains a SQLite-based test result capture system for comparing deobfuscation outputs across different test runs.

## Overview

The test capture system provides:

1. **SQLite Database** - Stores test results at `tests/system/.test_results.db`
2. **Pytest Plugin** - Automatically captures results when using `--capture-to-db`
3. **CLI Tool** - Query and compare results via command-line
4. **Fixture API** - Manual capture in test code via `db_capture` fixture

## Quick Start

### 1. Capture Test Results

Run your tests with the `--capture-to-db` flag:

```bash
# Capture results from test_libdeobfuscated.py
pytest tests/system/test_libdeobfuscated.py --capture-to-db -v

# Capture results from test_libdeobfuscated_dsl.py
pytest tests/system/test_libdeobfuscated_dsl.py --capture-to-db -v

# Capture from both suites
pytest tests/system/test_libdeobfuscated*.py --capture-to-db -v
```

### 2. Query Results

Use the CLI to explore captured results:

```bash
# List all functions tested
python -m tests.system.test_capture list-functions

# Get results for a specific function
python -m tests.system.test_capture get-function test_chained_add

# Compare two test suites
python -m tests.system.test_capture compare-suites \
    test_libdeobfuscated.py \
    test_libdeobfuscated_dsl.py

# Show recent test runs
python -m tests.system.test_capture recent --limit 20

# Show database statistics
python -m tests.system.test_capture stats
```

## Database Schema

The database captures:

### Test Results Table

| Column | Type | Description |
|--------|------|-------------|
| `test_suite` | TEXT | Test file name (e.g., `test_libdeobfuscated.py`) |
| `test_name` | TEXT | Test function name (e.g., `test_simplify_chained_add`) |
| `test_class` | TEXT | Test class name (e.g., `TestLibDeobfuscated`) |
| `function_name` | TEXT | Function being tested (e.g., `test_chained_add`) |
| `binary_name` | TEXT | Binary file (e.g., `libobfuscated.dylib`) |
| `function_address` | TEXT | Function address in hex |
| `code_before` | TEXT | Obfuscated pseudocode |
| `code_after` | TEXT | Deobfuscated pseudocode |
| `code_changed` | BOOLEAN | Did deobfuscation change code? |
| `rules_fired` | TEXT | JSON list of rule names that fired |
| `stats_dict` | TEXT | JSON of full statistics dictionary |
| `optimizer_usage` | TEXT | JSON of optimizer usage counts |
| `cfg_rule_usage` | TEXT | JSON of CFG rule usage |
| `passed` | BOOLEAN | Test passed? |
| `error_message` | TEXT | Error message if failed |
| `timestamp` | DATETIME | When test was run |
| `test_duration` | REAL | Test duration in seconds |

### Views

- **`latest_results`** - Most recent result for each function/suite combination
- **`function_coverage`** - Coverage statistics per function

## CLI Commands

### `list-functions`

Lists all functions tested with coverage information:

```bash
$ python -m tests.system.test_capture list-functions

Function                                 Suites Runs  Passed Test Suites
====================================================================================================
test_and                                 2      10    10     test_libdeobfuscated.py,test_libdeobfuscated_dsl.py
test_chained_add                         2      15    14     test_libdeobfuscated.py,test_libdeobfuscated_dsl.py
test_xor                                 1      5     5      test_libdeobfuscated_dsl.py
...
```

### `get-function <name>`

Shows all results for a specific function:

```bash
$ python -m tests.system.test_capture get-function test_chained_add --limit 3

================================================================================
Result 1 of 3
================================================================================
Test: test_libdeobfuscated_dsl.py :: test_core_deobfuscation[chained_add]
Function: test_chained_add
Passed: True
Timestamp: 2024-12-01 15:30:45
Code Changed: True

Rules Fired (5):
  - Rule_AddCstToAddCst
  - Rule_TwoSubOfNeg
  - Rule_CstXorXor
  ...

Deobfuscated Code:
__int64 __fastcall test_chained_add(__int64 a1)
{
    return 2 * a1[1] + 0x33;
}
```

### `compare-suites <suite1> <suite2>`

Compares results between two test suites:

```bash
$ python -m tests.system.test_capture compare-suites \
    test_libdeobfuscated.py \
    test_libdeobfuscated_dsl.py

Comparison: test_libdeobfuscated.py vs test_libdeobfuscated_dsl.py
================================================================================
Total functions in test_libdeobfuscated.py: 12
Total functions in test_libdeobfuscated_dsl.py: 25
Common functions: 10
Only in test_libdeobfuscated.py: 2
Only in test_libdeobfuscated_dsl.py: 15

Functions only in test_libdeobfuscated.py:
  - constant_folding_test1
  - outlined_helper_1

Functions only in test_libdeobfuscated_dsl.py:
  - abc_xor_dispatch
  - nested_simple
  ...

Differences in common functions (3):
  test_chained_add:
    Passed in suite1: True
    Passed in suite2: True
    Code changed: False
    Rules only in suite1: Rule_Deprecated_Pattern
    Rules only in suite2: Rule_NewOptimizer_V2
```

### `recent --limit N`

Shows recent test runs:

```bash
$ python -m tests.system.test_capture recent --limit 10

Timestamp            Suite                          Function                       Passed  Duration
========================================================================================================================
2024-12-01 15:30:45  test_libdeobfuscated_dsl.py    test_chained_add               ✓       2.150s
2024-12-01 15:30:43  test_libdeobfuscated_dsl.py    test_xor                       ✓       1.980s
2024-12-01 15:30:41  test_libdeobfuscated.py        test_simplify_chained_add      ✓       2.340s
...
```

### `stats`

Shows database statistics:

```bash
$ python -m tests.system.test_capture stats

Database Statistics:
  Total tests: 150
  Test suites: 2
  Functions tested: 35
  Passed: 145
  Skipped: 3
  Failed: 2
  Average duration: 2.150s
```

## Manual Capture in Tests

You can manually capture results using the `db_capture` fixture:

```python
def test_my_function(self, d810_state, db_capture, pseudocode_to_string):
    """Example test with manual capture."""
    func_ea = get_func_ea("my_function")

    with d810_state() as state:
        # Decompile before
        state.stop_d810()
        decompiled_before = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
        code_before = pseudocode_to_string(decompiled_before.get_pseudocode())

        # Decompile after
        state.start_d810()
        decompiled_after = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
        code_after = pseudocode_to_string(decompiled_after.get_pseudocode())

        # Manual assertions
        assert code_before != code_after

        # Capture result to database
        db_capture.record(
            function_name="my_function",
            code_before=code_before,
            code_after=code_after,
            stats=state.stats,
            passed=True,
            function_address=hex(func_ea),
        )
```

## Integration with DSL Tests

The DSL test runner (`run_deobfuscation_test`) automatically captures results when `db_capture` fixture is provided:

```python
@pytest.mark.parametrize("case", TEST_CASES, ids=lambda c: c.test_id)
def test_deobfuscation(
    self,
    case,
    d810_state,
    pseudocode_to_string,
    code_comparator,
    db_capture,  # Add this parameter
):
    """Test with automatic capture."""
    run_deobfuscation_test(
        case=case,
        d810_state=d810_state,
        pseudocode_to_string=pseudocode_to_string,
        code_comparator=code_comparator,
        db_capture=db_capture,  # Pass it to runner
    )
```

## Use Cases

### 1. Track Regression

Compare current run against historical baseline:

```bash
# Capture baseline
pytest tests/system/test_libdeobfuscated_dsl.py --capture-to-db -v

# Make changes to d810
# ... edit code ...

# Run again and compare
pytest tests/system/test_libdeobfuscated_dsl.py --capture-to-db -v
python -m tests.system.test_capture get-function test_chained_add --limit 5
```

### 2. Compare Implementation Approaches

Compare results from different test suites testing the same functions:

```bash
# Capture from both suites
pytest tests/system/test_libdeobfuscated.py --capture-to-db -v
pytest tests/system/test_libdeobfuscated_dsl.py --capture-to-db -v

# Compare
python -m tests.system.test_capture compare-suites \
    test_libdeobfuscated.py \
    test_libdeobfuscated_dsl.py \
    --show-code
```

### 3. Identify Coverage Gaps

Find functions tested by only one suite:

```bash
python -m tests.system.test_capture list-functions | grep "1      "
```

### 4. Rule Usage Analysis

Query which rules fire for specific functions:

```bash
python -m tests.system.test_capture get-function test_chained_add | grep "Rules Fired"
```

## Advanced Queries

You can directly query the SQLite database for custom analysis:

```bash
sqlite3 tests/system/.test_results.db
```

Example queries:

```sql
-- Find functions that changed code most recently
SELECT function_name, test_suite, timestamp
FROM test_results
WHERE code_changed = 1
ORDER BY timestamp DESC
LIMIT 10;

-- Find most commonly fired rules
SELECT json_each.value as rule_name, COUNT(*) as count
FROM test_results, json_each(test_results.rules_fired)
GROUP BY rule_name
ORDER BY count DESC;

-- Find functions with failures
SELECT function_name, test_suite, error_message, timestamp
FROM test_results
WHERE passed = 0
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
ON t1.function_name = t2.function_name
WHERE rules_suite1 != rules_suite2;
```

## Database Maintenance

### Reset Database

```bash
rm tests/system/.test_results.db
```

### Export Results

```bash
# Export to JSON
sqlite3 tests/system/.test_results.db \
    "SELECT json_object(
        'function', function_name,
        'code_after', code_after,
        'rules', json(rules_fired)
    ) FROM test_results" | jq

# Export to CSV
sqlite3 -header -csv tests/system/.test_results.db \
    "SELECT test_suite, function_name, passed, timestamp FROM test_results" \
    > results.csv
```

## Troubleshooting

### No results captured

- Ensure `--capture-to-db` flag is used
- Check that `db_capture` fixture is included in test parameters
- Verify database exists at `tests/system/.test_results.db`

### Database locked errors

- Close any SQLite browser/editor that has the database open
- Ensure only one test run is writing to DB at a time

### Missing function data

- The automatic plugin capture relies on `user_properties` being set
- For DSL tests, ensure `db_capture` is passed to `run_deobfuscation_test()`
- For manual tests, ensure `db_capture.record()` is called

## Implementation Details

### Files

- `tests/system/test_capture.py` - Main implementation
  - `TestResultCapture` - Context manager for capturing results
  - `TestResultQuery` - Query helper class
  - `CapturePlugin` - Pytest plugin for automatic capture
  - CLI interface via `python -m tests.system.test_capture`

- `tests/system/conftest.py` - Pytest integration
  - `--capture-to-db` option registration
  - `db_capture` fixture definition
  - Plugin registration in `pytest_configure`

- `src/d810/testing/runner.py` - DSL test runner integration
  - `run_deobfuscation_test()` accepts `db_capture` parameter
  - Automatically calls `db_capture.record()` on success

### Database Location

`.test_results.db` is created in `tests/system/` and is git-ignored by default.

### Schema Migrations

The database includes a `schema_version` table for future migrations. Current version is 1.
