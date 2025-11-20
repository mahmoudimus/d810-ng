---
name: project-debugging
description: Systematic debugging for Project - four-phase framework (root cause investigation, pattern analysis, hypothesis testing, implementation) with state inspection, debugging, sync issues, and troubleshooting
version: 2025-11-05
related_skills:
  - project-verification (verify fix with full test suite)
  - ci-debugging (debug GitHub Actions failures)
  - using-superpowers (announce skill usage)
---

# Systematic Debugging for Project

## Overview

Random fixes waste time. Quick patches mask underlying issues.

**Core principle:** ALWAYS find root cause before attempting fixes.

**project-specific:** Debug state sync issues, decorator problems, mismatches, and race conditions.

## The Iron Law

```
NO FIXES WITHOUT ROOT CAUSE INVESTIGATION FIRST
```

If you haven't completed Phase 1, you cannot propose fixes.

## When to Use

**Any technical issue:**
- Test failures 
- UI not updating (Python Qt)
- Build failures
- Decorator issues
- Race conditions

## The Four Phases

### Phase 1: Root Cause Investigation

**1. Read Error Messages Carefully**


**2. Reproduce Consistently**

**3. Check Recent Changes**

```bash
git diff HEAD~1               # Last commit
git log --oneline -5          # Recent commits
git diff --stat origin/master # All changes on branch
```

**4. Gather Evidence**


**5. Trace Data Flow**

Find the layer where data stops flowing correctly.

### Phase 2: Pattern Analysis

**1. Find Working Examples**


**2. Compare Against References**

Read docs COMPLETELY. Update markdown files with any discoveries.

**3. Identify Differences**

Use diff tools:

```bash
# Compare your new system to existing one
diff ...
```

```bash
# Compare your previous checked in system  against other branches
git diff ...
```
**4. Understand Dependencies**

### Phase 3: Hypothesis and Testing

**1. Form Single Hypothesis**

**Good:**
- "X doesn't work because Y decorator is missing"
- "X doesn't update because Y listener not set up"
- "Test fails because X does not register, need how do the other tests work instead?"

**Bad:**
- Too vague
- Something wrong with xx (blaming framework)
- "Might be a race condition" (guessing)

**2. Test Minimally**

ONE change at a time.

**3. Verify Before Continuing**

```bash
# Did it work?
python -m unittest discover -s tests.unit -t . -v

# Python's built in unit test runner

python -m unittest discover -s tests/unit -p test_*.py -t .

# using pytest if installed 
python -m pytest tests/ -v --tb=short --cov=src/ida_taskr --cov-report=html --cov-report=term
```

# If NO: Form NEW hypothesis
# If YES: Proceed to Phase 4
```

**4. When You Don't Know**

Say: "I don't understand why X isn't working"

Don't say: "Let me try adding more Y and see what happens"

Ask for help or research in:
- markdown docs 
- Existing codebase examples

### Phase 4: Implementation

**1. Create Failing Test**

**2. Implement Single Fix**

NO "while I'm here" improvements.

**3. Verify Fix**

```bash
# Run the specific test
python -m unittest tests.unit.test_utils.TestUtils.test_roundtrip_conversion -v

# THEN:

# Run full suite using python's built in unit test runner
python -m unittest discover -s tests.unit -t . -v
OR
# using pytest if installed 
python -m pytest tests/ -v --tb=short --cov=src/ida_taskr --cov-report=html --cov-report=term
```

**4. If 3+ Fixes Failed**

**Pattern:**
- Each fix reveals new issue
- "Need massive refactoring" for simple feature
- Fixes create new symptoms elsewhere

**STOP and question:**
- Is this architecture sound?
- Should we refactor instead of patching?
- Discuss with team before attempting fix #4

### 6. Logging Best Practices

```python
# GOOD: Scoped, structured
import logging

logger = logging.getLogger("ShieldManager")
logger.info("update: strength=%s rate=%s", self.state.shield.strength, rechargeRate)

# BAD: Generic, unclear
logger.info("shield %s", shield)
```

Use prefixes: `[CLIENT]`, `[SERVER]`, `[MANAGER]`, `[<FUNCTION_NAME>]`

## Integration with Other Skills

- **project-verification** - Verify fix with full test suite
- **ci-debugging** - Debug GitHub Actions failures when tests pass locally but fail in CI
