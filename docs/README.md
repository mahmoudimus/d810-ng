# D810-NG Documentation

Complete documentation for the D810-NG IDA Pro deobfuscation plugin.

## Table of Contents

### For Users

- [Main README](../README.md) - Installation and basic usage
- [Configuration Guide](#) - TODO: How to configure d810 for your project

### For Developers

- **[DSL Migration Guide](DSL_MIGRATION.md)** - Complete guide to the declarative pattern matching system
  - Architecture overview
  - DSL reference
  - Migration from old rules
  - Testing with Z3
  - Design decisions

- [Testing Infrastructure](TESTING_INSTRUMENTATION.md) - How the test system works

- [Refactoring Strategy](../REFACTORING.md) - Overall architecture refactoring plan
  - Pattern matching rules (✅ Complete)
  - Flow optimization (❌ Not started)

### Project History

- [Migration Complete Summary](archive/MIGRATION_COMPLETE.md) - Final status of DSL migration
- [Retrospective](archive/RETROSPECTIVE.md) - Lessons learned from the migration

## Quick Links

### Creating New Rules

See [DSL Migration Guide - Quick Start](DSL_MIGRATION.md#dsl-reference) for:
- Basic rule structure
- Using variables and constants
- Adding constraints
- Testing your rules

### Running Tests

```bash
# Test all rules (no IDA required!)
pytest tests/unit/mba/test_verifiable_rules.py -v

# Test specific rule
pytest tests/unit/mba/test_verifiable_rules.py::test_rule_is_correct[RuleName] -v

# System tests (requires IDA)
pytest tests/system/optimizers/test_verifiable_rules.py -v
```

### Migration Statistics

- **172 total rules** (170 correct + 2 known_incorrect)
- **12 modules** fully migrated
- **100% test parity** with original system
- **60% code reduction** in rule definitions
- **100% Z3 verification** for correct rules

## Development Guidelines

### Adding New Rules

1. Create your rule in the appropriate file under `src/d810/mba/rules/` (e.g., `xor.py`, `add.py`)
2. Use the declarative DSL (see [DSL Reference](DSL_MIGRATION.md#dsl-reference))
3. Run tests: `pytest tests/unit/mba/test_verifiable_rules.py -k "YourRule" -v`
4. Your rule is automatically registered and tested!

### Code Organization

```
d810-ng/
├── docs/                    # All documentation (you are here)
│   ├── README.md           # This file
│   ├── DSL_MIGRATION.md    # Complete DSL guide
│   └── archive/            # Historical documents
├── src/d810/
│   ├── mba/                # Pure symbolic MBA package (no IDA dependency)
│   │   ├── dsl.py          # Symbolic expression DSL
│   │   ├── rules/          # Pure rule definitions (177 rules)
│   │   │   ├── _base.py    # VerifiableRule base class
│   │   │   ├── xor.py      # XOR rules
│   │   │   └── ...         # Other rule modules
│   │   └── backends/
│   │       ├── z3.py       # Z3 SMT verification
│   │       └── ida.py      # IDA pattern adapter
│   ├── optimizers/
│   │   ├── extensions.py   # Context-aware DSL extensions (IDA-specific)
│   │   └── microcode/instructions/pattern_matching/
│   │       └── experimental.py  # Rules requiring IDA context
│   └── ...
├── tests/
│   ├── unit/mba/
│   │   └── test_verifiable_rules.py  # Unit tests (no IDA required)
│   └── system/             # Integration tests (requires IDA)
└── scripts/                # Utility scripts
```

### Best Practices

1. **Use descriptive rule names**: `Xor_HackersDelightRule_1` not `Rule123`
2. **Add docstrings**: Explain the mathematical identity and provide proof/reference
3. **Keep it simple**: Don't add features that aren't needed
4. **Test locally**: Run verification before committing
5. **Document constraints**: Clearly explain when a rule applies

## Contributing

### Before You Start

1. Read the [DSL Migration Guide](DSL_MIGRATION.md)
2. Review existing rules in `src/d810/mba/rules/`
3. Understand the [architecture](../README.md#architecture-pure-rules-vs-ida-specific-rules)

### Submitting Changes

1. Ensure all tests pass: `pytest tests/unit/mba/test_verifiable_rules.py -v`
2. Add tests for new functionality
3. Update documentation if needed
4. Follow the existing code style

## FAQ

### Why use Z3 for verification?

Z3 exhaustively checks all possible input values symbolically. This is more reliable than manual test cases and finds edge cases automatically.

### What if my rule can't be verified by Z3?

Use the `SKIP_VERIFICATION = True` flag and document why verification isn't possible. Then add manual test cases.

### How do I know if my rule is correct?

Run the test suite. If Z3 verification passes, your rule is mathematically correct for all possible inputs.

### Can I use the old imperative style?

No - the old `PatternMatchingRule` has been fully replaced by `VerifiableRule`. See the migration guide for how to convert old rules.

## Support

- File issues on GitHub
- Check existing documentation in `docs/`
- Review similar rules in `src/d810/mba/rules/`

---

*Last updated: 2025-11-25*
