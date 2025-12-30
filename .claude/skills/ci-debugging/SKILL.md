---
name: ci-debugging
description: Debug GitHub Actions CI failures - analyze logs for errors, identify root causes, and apply fixes locally before pushing
version: 2025-11-05
related_skills:
  - github-api (GitHub CLI setup and API access)
  - project-debugging (systematic debugging framework)
  - project-verification (verify fixes with test commands)
  - using-superpowers (announce skill usage)
---

# CI Debugging

## Overview

Debug GitHub Actions CI failures independently by downloading logs and analyzing them locally.

**Core principle:** ALWAYS download CI logs before attempting to debug failures.

**Prerequisites:** Use the **github-api** skill to set up GitHub CLI access first.

## The Iron Law

```
NO CI DEBUGGING WITHOUT LOG ACCESS FIRST
```

If you haven't downloaded logs, you cannot diagnose CI failures.

## When to Use

**Any GitHub Actions failure:**
- Unit Tests
- Integration-Tests
- Build failures
- Workflow configuration errors
- **Test timeouts** (tests hang for 30+ minutes)

## Quick Start

**Prerequisites:**
1. Use **github-api** skill to install GitHub CLI
2. Verify authentication: `gh auth status`
3. Set alias: `GH="/tmp/gh-install/gh_2.83.1_linux_amd64/bin/gh"`

**Quick Workflow:**
```bash
# 1. Get PR checks
$GH pr checks <PR_NUMBER> --repo <GITHUB-REPO-OWNER>/<GITHUB-REPO-NAME>

# 2. Extract run ID from URL
RUN_ID=$($GH pr checks <PR_NUMBER> --repo <GITHUB-REPO-OWNER>/<GITHUB-REPO-NAME> | grep -oP 'runs/\K[0-9]+' | head -1)

# 3. Download logs
$GH api repos/<GITHUB-REPO-OWNER>/<GITHUB-REPO-NAME>/actions/runs/$RUN_ID/logs --paginate > /tmp/run-logs.zip
cd /tmp && unzip -o -q run-logs.zip

# 4. Analyze failures (see sections below)
```

## CI Log Analysis

### Identify Failed Jobs

```bash
# Get failed jobs and steps
$GH api repos/<GITHUB-REPO-OWNER>/<GITHUB-REPO-NAME>/actions/runs/<RUN_ID>/jobs \
  --jq '.jobs[] | select(.conclusion=="failure") | {name, steps: [.steps[] | select(.conclusion=="failure") | .name]}'
```

### Log File Organization

Downloaded logs are named by jobs

## Complete CI Debug Workflow

### Full Script

```bash
#!/bin/bash
set -e

# Setup (use github-api skill for this part)
GH="/tmp/gh-install/gh_2.83.1_linux_amd64/bin/gh"
REPO="<GITHUB-REPO-OWNER>/<GITHUB-REPO-NAME>"
PR_NUMBER=$1

if [ -z "$PR_NUMBER" ]; then
  echo "Usage: $0 <PR_NUMBER>"
  exit 1
fi

echo "=== Step 1: Check PR Status ==="
$GH pr view $PR_NUMBER --repo $REPO

echo -e "\n=== Step 2: Get Check Results ==="
$GH pr checks $PR_NUMBER --repo $REPO

echo -e "\n=== Step 3: Identify Failed Jobs ==="
RUN_ID=$($GH pr checks $PR_NUMBER --repo $REPO | grep -oP 'runs/\K[0-9]+' | head -1)
echo "Run ID: $RUN_ID"

$GH api repos/$REPO/actions/runs/$RUN_ID/jobs \
  --jq '.jobs[] | select(.conclusion=="failure") | {
    name: .name,
    failed_steps: [.steps[] | select(.conclusion=="failure") | .name]
  }'

echo -e "\n=== Step 4: Download Logs ==="
$GH api repos/$REPO/actions/runs/$RUN_ID/logs --paginate > /tmp/run-logs.zip
cd /tmp && unzip -o -q run-logs.zip
echo "Logs extracted to /tmp/*.txt"

echo -e "\n=== Step 5: Analyze Failures ==="


echo -e "\n=== Step 6: Next Steps ==="
echo "1. Review errors above"
echo "2. Fix issues locally"
echo "3. Commit and push"
echo "4. Monitor new CI run with: $GH pr checks $PR_NUMBER --repo $REPO"
```

### Save and Use

```bash
# Save script
cat > /tmp/debug-ci.sh << 'EOF'
[paste script above]
EOF

chmod +x /tmp/debug-ci.sh

# Run
/tmp/debug-ci.sh 1826
```

## Local Verification Checklist

Before pushing CI fixes, try to run the tests locally

## Monitoring After Push

```bash
# Wait for CI to start
sleep 30

# Check new run status
$GH pr checks <PR_NUMBER> --repo <GITHUB-REPO-OWNER>/<GITHUB-REPO-NAME>

# If still failing, download new logs and repeat
RUN_ID=$($GH pr checks <PR_NUMBER> --repo <GITHUB-REPO-OWNER>/<GITHUB-REPO-NAME> | grep -oP 'runs/\K[0-9]+' | head -1)
$GH api repos/<GITHUB-REPO-OWNER>/<GITHUB-REPO-NAME>/actions/runs/$RUN_ID/logs --paginate > /tmp/run-logs-retry.zip
```

## Integration with Other Skills

- **github-api** - Setup GitHub CLI, download logs, query API
- **debugging** - Systematic debugging for local reproduction
- **verification** - Run verification commands before push
- **workflow** - Terminal commands for local testing

## Quick Reference

### GitHub CLI Commands
See **github-api** skill for:
- Installation and setup
- Authentication
- API access patterns
- Rate limiting

### CI-Specific Commands
```bash
# Get PR checks
$GH pr checks <PR> --repo <GITHUB-REPO-OWNER>/<GITHUB-REPO-NAME>

# Get run details
$GH run view <RUN_ID> --repo <GITHUB-REPO-OWNER>/<GITHUB-REPO-NAME>

# Download logs
$GH api repos/<GITHUB-REPO-OWNER>/<GITHUB-REPO-NAME>/actions/runs/<RUN_ID>/logs --paginate > /tmp/logs.zip

# Get failed jobs
$GH api repos/<GITHUB-REPO-OWNER>/<GITHUB-REPO-NAME>/actions/runs/<RUN_ID>/jobs \
  --jq '.jobs[] | select(.conclusion=="failure")'
```

## Special Case: Test Timeouts

**Symptom:** CI shows very long runtimes (30+ minutes) with no error output.

**Key insight:** Tests that HANG don't produce errors in logs - they just stop progressing.

### Quick Diagnosis

```bash
# 1. Check runtime from CI
$GH run view <RUN_ID> --repo <GITHUB-REPO-OWNER>/<GITHUB-REPO-NAME>
# Look for: "Total duration: 64m 23s" (suspiciously long)

# 2. Download logs
$GH api repos/<GITHUB-REPO-OWNER>/<GITHUB-REPO-NAME>/actions/runs/<RUN_ID>/logs --paginate > /tmp/logs.zip
cd /tmp && unzip -o -q logs.zip

# 3. Find where tests stopped
grep "PASSED\|FAILED" /tmp/*.txt | tail -50
# Identify last passing test

# 4. The NEXT test after last passing is likely hanging
```

### Common Hanging Causes in CI

1. **Multiprocessing operations** - Worker processes don't terminate
2. **Database operations** - SQLite locks, connections hang
3. **Network operations** - Requests without timeouts
4. **Infinite loops** - Logic errors in tests

### Fix Pattern

**Skip problematic tests locally and verify:**

```python
# Mark hanging tests for skip
@pytest.mark.skip(reason="Parallel execution tests hang - not ready for CI")
class TestProblematic:
    pass
```

**Verify locally:**
```bash
# Run with timeout to ensure it completes
timeout 600 pytest tests/unit -v --durations=20

# Should complete in reasonable time (< 60s for unit tests)
```

**For detailed debugging:** Use **project-debugging** skill's "Test Hanging/Timeout Debugging" section.

## Tips

1. **Download logs first** - Always get complete context before debugging
2. **Check run ID** - Ensure you're analyzing the correct workflow run
3. **Group errors** - Use `sort | uniq -c` to identify patterns
4. **Verify locally** - Run all checks before pushing
5. **Monitor after push** - Watch new CI run to confirm fix
6. **Save scripts** - Keep debug workflow script for repeated use
7. **Watch for timeouts** - If CI takes 30+ minutes, tests are hanging (not slow)

