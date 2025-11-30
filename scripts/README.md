# D-810 ng Scripts

This directory contains utility scripts for the D-810 ng project.

## Available Scripts

### check_github_actions.py

A comprehensive script to check the status of GitHub Actions workflows for commits, branches, or pull requests.

**Features:**
- Check workflow status for the most recent commit
- Check status for specific commits by SHA
- Check status for specific pull requests
- Check status for specific branches
- Colorful emoji-based status display
- Detailed workflow information including timestamps and URLs

**Usage:**

```bash
# Check status for the most recent commit on the current branch
python scripts/check_github_actions.py

# Check status for a specific commit
python scripts/check_github_actions.py --commit abc123def

# Check status for a specific pull request
python scripts/check_github_actions.py --pr 2

# Check status for a specific branch
python scripts/check_github_actions.py --branch main

# Limit the number of results displayed
python scripts/check_github_actions.py --pr 2 --limit 10
```

**Environment Variables:**
- `GITHUB_TOKEN`: GitHub personal access token (optional for public repositories, required for private repos or higher rate limits)

**Example Output:**

```
📦 Repository: mahmoudimus/d810-ng

🔍 Checking PR #2...
   Branch: claude/review-d810-refactoring-01JDgmKS3VoevvzFXYgixZoJ
   Commit: b3bb8b9

📊 Found 3 workflow run(s):

1.   ✅ Success
  Name: d810-ng tests
  Branch: claude/review-d810-refactoring-01JDgmKS3VoevvzFXYgixZoJ
  Commit: b3bb8b9
  Updated: 2025-11-19 03:49:17 UTC
  URL: https://github.com/mahmoudimus/d810-ng/actions/runs/19489104339

============================================================
📈 Summary:
  ✅ success: 3

✅ Most recent workflow: SUCCESS
```

**Exit Codes:**
- `0`: Success or in progress
- `1`: Most recent workflow failed

### converter.py

A LibCST-based code transformer that converts classes inheriting from `PatternMatchingRule` to use property methods instead of class attributes for `PATTERN` and `REPLACEMENT_PATTERN`.

**Usage:**

```bash
# Preview changes for a single file
python scripts/converter.py path/to/file.py

# Apply changes in-place
python scripts/converter.py --in-place path/to/file.py

# Process entire directory
python scripts/converter.py --in-place src/d810/
```

### ununicode.py

A utility script for handling Unicode transformations (exact purpose depends on implementation).

## Test Scripts

### `run_integration_tests.sh`
Runs integration tests against sample binaries.

**Usage:**
```bash
./scripts/run_integration_tests.sh
```

### `test_with_docker.sh`
Runs tests inside a Docker container with IDA Pro installed.

**Usage:**
```bash
./scripts/test_with_docker.sh
```

## Migration Scripts

Located in `scripts/migration/` - these were used during the DSL migration and are kept for reference.

### `bulk_migrate_cst.py`
Automated migration of constant simplification rules from imperative to declarative DSL.

### `constraint_dsl_implementation.py`
Prototype implementation of constraint system for VerifiableRule.

### `dsl_constraints_proposal.py`
Design proposal for declarative constraint syntax.

### `fol_converter_poc.py`
Proof of concept for First-Order Logic conversion (not used in final implementation).

### `migrate_dynamic_const.py`
Helper script to migrate rules using DynamicConst patterns.

### `test_constraint*.py`
Various test scripts for constraint system validation.

### `test_imports.py`
Module import testing utility.

**Note:** Most migration scripts are historical and kept for reference. The DSL migration is complete.

## Development

When adding new scripts to this directory:

1. Add appropriate shebang (`#!/usr/bin/env python3`) at the top
2. Include comprehensive docstrings
3. Add command-line argument parsing for flexibility
4. Update this README with usage instructions
5. Make scripts executable: `chmod +x scripts/your_script.py`
6. Place migration tools in `scripts/migration/`
