# AGENTS.md

## Issue Tracking with bd (beads)

**IMPORTANT**: This project uses **bd (beads)** for ALL issue tracking. Do NOT use markdown TODOs, task lists, or other tracking methods.

### Why bd?

- Dependency-aware: Track blockers and relationships between issues
- Git-friendly: Auto-syncs to JSONL for version control
- Agent-optimized: JSON output, ready work detection, discovered-from links
- Prevents duplicate tracking systems and confusion

### Quick Start

**Check for ready work:**
```bash
bd ready --json
```

**Create new issues:**
```bash
bd create "Issue title" -t bug|feature|task -p 0-4 --json
bd create "Issue title" -p 1 --deps discovered-from:d810ng-abc --json
```

**Claim and update:**
```bash
bd update d810ng-xyz --status in_progress --json
bd update d810ng-xyz --priority 1 --json
```

**Complete work:**
```bash
bd close d810ng-xyz --reason "Completed" --json
```

### Issue Types

- `bug` - Something broken
- `feature` - New functionality
- `task` - Work item (tests, docs, refactoring)
- `epic` - Large feature with subtasks
- `chore` - Maintenance (dependencies, tooling)

### Priorities

- `0` - Critical (security, data loss, broken builds)
- `1` - High (major features, important bugs)
- `2` - Medium (default, nice-to-have)
- `3` - Low (polish, optimization)
- `4` - Backlog (future ideas)

### Workflow for AI Agents

1. **Check ready work**: `bd ready` shows unblocked issues
2. **Claim your task**: `bd update d810ng-xxx --status in_progress`
3. **Work on it**: Implement, test, document
4. **Discover new work?** Create linked issue:
   - `bd create "Found bug" -p 1 --deps discovered-from:d810ng-xxx`
5. **Complete**: `bd close d810ng-xxx --reason "Done"`

Note: In stealth mode, issue state is local only (not synced via git).

### Auto-Sync (Disabled)

Auto-sync is disabled in this repository (stealth mode). The `.beads/` directory is globally gitignored, so issue state remains local to each machine.

### Important Rules

- Use bd for ALL task tracking
- Always use `--json` flag for programmatic use
- Do NOT run `bd sync` (stealth mode - see below)
- Do NOT create markdown TODO lists
- Do NOT commit `.beads/` directory (globally gitignored)

### Stealth Mode

This repository runs beads in **stealth mode** (local only, not git-synced):
- `.beads/` is globally gitignored
- Do NOT run `bd sync` - it will fail
- Use local commands only: `bd list`, `bd create`, `bd update`, `bd close`
- Issue state is local to each developer's machine

### Known Issues & Workarounds

#### Hyphenated prefix bug (bd 0.25.1 - 0.26.0)

**Symptom:**
```
Import failed: prefix mismatch detected: database uses 'd810-ng-' but found issues with prefixes: [d810- (4 issues)]
```
or:
```
Import failed: failed to rename prefixes: cannot rename issue d810-ng-iid: non-numeric suffix 'ng-iid'
```

**Cause:** Bug in bd 0.25.1-0.26.0 where hyphenated prefixes (like `d810-ng-`) are incorrectly parsed. The parser splits on the first hyphen, so `d810-ng-e68` becomes prefix `d810-` + suffix `ng-e68` instead of `d810-ng-` + `e68`. The `--rename-on-import` flag is also broken for this reason.

**Permanent fix:** Reinitialize with a non-hyphenated prefix:
```bash
# Backup existing issues
bd list --json | jq -c '.[]' > /tmp/beads_backup.jsonl

# Reinitialize with non-hyphenated prefix
rm -rf .beads
bd init --prefix d810ng

# Fix prefixes in backup and import
sed 's/"d810-ng-/"d810ng-/g' /tmp/beads_backup.jsonl > /tmp/beads_fixed.jsonl
bd import -i /tmp/beads_fixed.jsonl

# Export to sync JSONL
rm -f .beads/issues.jsonl
bd list --json | jq -c '.[]' > .beads/issues.jsonl

# Verify
bd doctor
```

This repository now uses prefix `d810ng` (no hyphen) to avoid this bug.
