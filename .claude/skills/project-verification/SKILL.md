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

### Unit & Integration Tests

```bash
# All tests using python's built-in unit test runner
python -m unittest discover -s tests.unit -t . -v

# Python's built in unit test runner

python -m unittest discover -s tests/unit -p test_*.py -t .

# using pytest if installed 
python -m pytest tests/ -v --tb=short --cov=src/ida_taskr --cov-report=html --cov-report=term
```

## Integration with Other Skills

- **project-debugging** - Debug failures systematically

## The Bottom Line

**"No shortcuts for verification."**

Run the commands. Read the output. THEN claim the result.

This is non-negotiable.
