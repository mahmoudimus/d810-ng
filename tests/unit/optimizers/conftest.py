"""Pytest configuration for optimizer tests.

This conftest uses the d810 registry scanner to automatically discover
and load all optimization rules, rather than requiring manual imports.
"""

import sys
import pathlib
import pytest

# Add src to path if running tests outside of installed package
repo_root = pathlib.Path(__file__).parent.parent.parent.parent
src_path = repo_root / "src"
if src_path.exists() and str(src_path) not in sys.path:
    sys.path.insert(0, str(src_path))


def pytest_configure(config):
    """Pytest hook called after command line options have been parsed."""
    # Register custom markers
    config.addinivalue_line(
        "markers",
        "pure_python: Tests that can run without IDA Pro (fast, no external dependencies)"
    )
    config.addinivalue_line(
        "markers",
        "requires_ida: Tests that require IDA Pro to run"
    )
    config.addinivalue_line(
        "markers",
        "slow: Slow tests (>10s) - typically Z3 verification"
    )


@pytest.fixture(scope="session", autouse=True)
def load_all_rules():
    """Automatically load all optimization rules using the scanner.

    This fixture runs once per test session and uses the d810 scanner
    infrastructure to discover and load all rule modules. This ensures:

    1. Rules are auto-registered via Registrant.__init_subclass__
    2. No manual imports needed in test files
    3. New rules are automatically included in tests
    4. Works the same way as IDA plugin loading

    The scanner is only used when running tests that need IDA types.
    For pure Python tests, rules can be created directly.
    """
    try:
        # Only try to scan if we're running IDA-dependent tests
        # For pure Python tests, this will fail and that's OK
        import d810
        from d810.ida_reloadable import _Scanner

        # Get the package path for pattern matching rules
        pattern_matching_path = repo_root / "src" / "d810" / "optimizers" / "microcode" / "instructions" / "pattern_matching"

        if pattern_matching_path.exists():
            # Scan and load all pattern matching rule modules
            # This triggers __init_subclass__ and populates RULE_REGISTRY
            _Scanner.scan(
                package_path=[str(pattern_matching_path)],
                prefix="d810.optimizers.microcode.instructions.pattern_matching.",
                callback=None,  # No callback needed - __init_subclass__ handles registration
                skip_packages=True,  # Only load .py files, not __pycache__
            )

            from d810.optimizers.rules import RULE_REGISTRY
            print(f"\n[test setup] Loaded {len(RULE_REGISTRY)} rules via scanner")
        else:
            print(f"\n[test setup] Pattern matching path not found: {pattern_matching_path}")

    except ImportError as e:
        # Running in pure Python mode - no IDA available
        # This is expected for pure_python tests
        print(f"\n[test setup] Scanner not available (pure Python mode): {e}")
        pass
