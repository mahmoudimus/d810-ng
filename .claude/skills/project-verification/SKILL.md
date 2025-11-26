---
name: project-verification
description: Evidence-based completion verification for Project - run actual test commands, check snapshots, verify types, and confirm build success before claiming work is complete; evidence before assertions always
version: 2025-11-05
related_skills:
  - project-debugging (verify fix worked)
  - ci-debugging (verify CI passes after push)
  - using-superpowers (announce skill usage)
---

# Verification Before Completion - Project

## Overview

Claiming work is complete without verification is dishonesty, not efficiency.

**Core principle:** "Evidence before claims, always."

**project-specific:** Run project commands, check all module tests, verify E2E snapshots.

## The Iron Law

```
NO COMPLETION CLAIMS WITHOUT FRESH VERIFICATION EVIDENCE
```

If you haven't run the verification command in this message, you cannot claim it passes.

## The Gate Function

```
BEFORE claiming any status:

1. IDENTIFY: Which Project command proves this claim?
2. RUN: Execute the EXACT command (fresh, complete)
3. READ: Full output, exit code, count failures
4. VERIFY: Does output confirm the claim?
   - If NO: State actual status with evidence
   - If YES: State claim WITH evidence
5. ONLY THEN: Make the claim

Skip any step = lying, not verifying
```

## Project Verification Commands

### Python Projects: unittest vs pytest

Many Python projects support BOTH test runners. Always verify with the method used by CI.

### Unit Tests (unittest - Python standard library)

**Basic discovery:**
```bash
# Discover and run all tests in tests/unit directory
python -m unittest discover -s tests/unit -p test_*.py -t . -v

# Alternative patterns:
python -m unittest discover -s tests.unit -t . -v
python -m unittest discover -s tests/ -p "test_*.py" -v
```

**Run specific tests:**
```bash
# Specific test module
python -m unittest tests.unit.test_utils -v

# Specific test class
python -m unittest tests.unit.test_utils.TestUtils -v

# Specific test method
python -m unittest tests.unit.test_utils.TestUtils.test_roundtrip_conversion -v
```

### Integration Tests (pytest - if installed)

**Basic usage:**
```bash
# All tests
pytest tests/ -v

# Specific directory
pytest tests/system/ -v

# Short traceback (easier to read)
pytest tests/ -v --tb=short

# Very verbose (full output)
pytest tests/ -vv
```

**Run specific tests:**
```bash
# Specific file
pytest tests/system/test_rule_tracking.py -v

# Specific class
pytest tests/system/test_rule_tracking.py::TestRuleFiring -v

# Specific test method
pytest tests/system/test_rule_tracking.py::TestRuleFiring::test_verify_refactored_modules_loaded -v
```

### Coverage Verification

**pytest with coverage plugin:**
```bash
# Generate HTML and terminal reports
pytest tests/ -v --tb=short \
  --cov=src/d810 \
  --cov-report=html \
  --cov-report=term

# Coverage for specific directory
pytest tests/system/ -v \
  --cov=src/d810/optimizers \
  --cov-report=html

# Show missing lines
pytest tests/ -v \
  --cov=src/d810 \
  --cov-report=term-missing

# Generate XML for CI
pytest tests/ -v \
  --cov=src/d810 \
  --cov-report=xml \
  --cov-report=html
```

**Coverage output locations:**
- HTML report: `htmlcov/index.html` (open in browser)
- XML report: `coverage.xml` (for CI/CD)
- Terminal: Printed to stdout

**unittest with coverage:**
```bash
# Install coverage if needed
pip install coverage

# Run with coverage
coverage run -m unittest discover -s tests/unit -t . -v
coverage report
coverage html

# View HTML report
# Open htmlcov/index.html in browser
```

### Verification Workflow

**Complete verification checklist:**
```bash
# 1. Run specific failing/changed test
pytest tests/module/test_feature.py::test_specific_case -v

# 2. Run all tests in changed module
pytest tests/module/ -v

# 3. Run full test suite
pytest tests/ -v --tb=short

# 4. Generate coverage report
pytest tests/ -v --cov=src/project --cov-report=html --cov-report=term

# 5. Check coverage threshold (if required)
pytest tests/ --cov=src/project --cov-fail-under=80

# 6. Verify no warnings
pytest tests/ -v --tb=short -W error

# 7. Check for broken tests
pytest tests/ -v --tb=short --maxfail=1  # Stop at first failure
```

### IDA Pro Projects (d810-ng example)

**See:** `tests/README.md` for full documentation.

**With IDA Python environment:**
```bash
# Unit tests (no IDA required)
PYTHONPATH=src pytest tests/unit/ -v --tb=short

# Integration tests (IDA required - headless via pytest)
/app/ida/.venv/bin/python3 -m pytest tests/system/ -v --tb=short

# Specific test with IDA
/app/ida/.venv/bin/python3 -m pytest \
  tests/system/test_rule_tracking.py::TestRuleFiring::test_verify_refactored_modules_loaded -v

# With coverage
/app/ida/.venv/bin/python3 -m pytest tests/system/ -v \
  --cov=src/d810 \
  --cov-report=html \
  --cov-report=term
```

### Expected Output Interpretation

**PASSED - All tests successful:**
```
tests/system/test_rule_tracking.py::TestRuleFiring::test_verify_refactored_modules_loaded PASSED
============ 1 passed in 2.34s ============
```

**FAILED - Some tests failed:**
```
tests/system/test_rule_tracking.py::TestRuleFiring::test_constant_folding FAILED
============ 1 passed, 4 failed in 6.53s ============
```

**Coverage report:**
```
Name                                  Stmts   Miss  Cover
---------------------------------------------------------
src/d810/manager.py                     150     12    92%
src/d810/optimizers/rules.py            89      5    94%
---------------------------------------------------------
TOTAL                                  2341    156    93%
```

**What to verify:**
- ✓ All modified code has passing tests
- ✓ Coverage maintained or improved
- ✓ No regressions in unrelated tests
- ✓ CI commands match local commands

## Practical Verification Example

**Real-world: Verifying d810-ng GUI import fix**

### Before claiming fix is complete:

**Step 1: Identify verification command**
```bash
# What test was failing?
# tests/system/test_rule_tracking.py::TestRuleFiring::test_verify_refactored_modules_loaded

# What command proves it passes now?
/app/ida/.venv/bin/python3 -m pytest \
  tests/system/test_rule_tracking.py::TestRuleFiring::test_verify_refactored_modules_loaded -v
```

**Step 2: Run the EXACT command**
```bash
$ /app/ida/.venv/bin/python3 -m pytest \
  tests/system/test_rule_tracking.py::TestRuleFiring::test_verify_refactored_modules_loaded -v

# Output:
tests/system/test_rule_tracking.py::TestRuleFiring::test_verify_refactored_modules_loaded PASSED [100%]
============ 1 passed in 2.45s ============
```

**Step 3: Read full output**
- Exit code: 0 (success)
- Test result: PASSED
- No errors or warnings related to imports
- Time: 2.45s

**Step 4: Verify claim with evidence**
✅ Can now claim: "The GUI import fix allows test_verify_refactored_modules_loaded to pass"

**Step 5: Verify no regressions**
```bash
# Run all tests in the file
$ /app/ida/.venv/bin/python3 -m pytest tests/system/test_rule_tracking.py -v

# Output:
tests/system/test_rule_tracking.py::TestRuleFiring::test_verify_refactored_modules_loaded PASSED
tests/system/test_rule_tracking.py::TestRuleFiring::test_constant_folding_refactored_rules FAILED
tests/system/test_rule_tracking.py::TestRuleFiring::test_mba_pattern_refactored_rules FAILED
tests/system/test_rule_tracking.py::TestRuleFiring::test_opaque_predicate_removal FAILED
tests/system/test_rule_tracking.py::TestRuleFiring::test_xor_pattern_refactored_rules FAILED
============ 1 passed, 4 failed, 216 warnings in 6.53s ============
```

**Analysis:**
- 1 test PASSED (our fix target) ✓
- 4 tests FAILED (expected - need binary samples) ✓
- 0 NEW failures ✓

✅ Can now claim: "Fix has no regressions - 4 failures are pre-existing and expected"

### What NOT to do:

**❌ Claiming without evidence:**
```
"I fixed the import issue, the test should pass now."
```
**Problem:** No verification run in this message. Cannot make this claim.

**❌ Assuming based on old output:**
```
"The test passed when I ran it 2 hours ago, so the fix works."
```
**Problem:** Code may have changed. Must run FRESH verification.

**❌ Partial verification:**
```
"I ran pytest and saw PASSED, so it works."
```
**Problem:** Didn't verify WHICH test passed. Could be wrong test.

**✅ Proper claim with evidence:**
```
"I verified the fix by running the specific failing test:

$ /app/ida/.venv/bin/python3 -m pytest tests/system/test_rule_tracking.py::TestRuleFiring::test_verify_refactored_modules_loaded -v

Result: PASSED ✓

I also verified no regressions by running the full test file. The 4 failures
are pre-existing (require binary samples) and expected.
```

### Coverage Verification Example

**Verifying coverage for new code:**

```bash
# Run with coverage
$ /app/ida/.venv/bin/python3 -m pytest tests/system/ -v \
  --cov=src/d810 \
  --cov-report=term \
  --cov-report=html

# Output includes:
Name                                          Stmts   Miss  Cover
-------------------------------------------------------------------
src/d810/manager.py                             156     12    92%
src/d810/optimizers/instrumentation.py           89      5    94%
src/d810/optimizers/rules.py                    234     23    90%
-------------------------------------------------------------------
TOTAL                                          2341    156    93%

Coverage HTML written to dir htmlcov
```

**Verification checklist:**
- ✓ Coverage report generated successfully
- ✓ Modified files (manager.py) have 92% coverage
- ✓ Overall coverage is 93% (above threshold)
- ✓ HTML report available in htmlcov/index.html

**Claim with evidence:**
```
"Coverage verification complete:
- manager.py: 92% coverage (12 uncovered lines are error handlers)
- Overall project: 93% coverage
- Coverage report: htmlcov/index.html"
```

### CI Verification

**After pushing fix, verify CI passes:**

```bash
# Wait for CI to run (30-60 seconds)
sleep 60

# Check CI status (using github-api skill)
$GH pr checks <PR_NUMBER> --repo mahmoudimus/d810-ng

# Output shows:
✓ Python Unit Tests (3.10)     - passing
✓ Python Unit Tests (3.11)     - passing
✓ Python Unit Tests (3.12)     - passing
✓ Python Unit Tests (3.13)     - passing
✓ IDA Pro Integration Tests    - passing
```

**Evidence-based claim:**
```
"CI verification complete. All checks passing:
- Python unit tests: PASSING on 3.10, 3.11, 3.12, 3.13
- IDA Pro integration tests: PASSING (previously 20+ consecutive failures)
- Fix confirmed working in CI environment"
```

## Integration with Other Skills

- **project-debugging** - Debug failures systematically before verification

## The Bottom Line

**"No shortcuts for verification."**

Run the commands. Read the output. THEN claim the result.

This is non-negotiable.
