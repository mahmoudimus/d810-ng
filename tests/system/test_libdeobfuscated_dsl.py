"""DSL-based tests for deobfuscation against libobfuscated binary.

This test module demonstrates the data-driven testing approach using
DeobfuscationCase dataclasses. Tests are defined in cases/libobfuscated.py
and executed by the run_deobfuscation_test runner.

This approach reduces boilerplate from ~50 lines per test to ~10 lines of data.

Example::

    # Define case (in cases/libobfuscated.py):
    DeobfuscationCase(
        function="test_chained_add",
        obfuscated_contains=["0xFFFFFFEF"],
        expected_code="__int64 __fastcall test_chained_add(...) { return 2 * a1[1] + 0x33; }",
        required_rules=["ArithmeticChain"],
    )

    # Test automatically runs for each case!

Override binary via environment variable:
    D810_TEST_BINARY=libobfuscated.dll pytest tests/system/test_libdeobfuscated_dsl.py
"""

import os
import platform

import pytest

import idaapi

from d810.testing import run_deobfuscation_test
from tests.system.cases.libobfuscated import LIBOBFUSCATED_CASES, SMOKE_TEST_CASES


def _get_default_binary() -> str:
    """Get default binary name based on platform, with env var override."""
    override = os.environ.get("D810_TEST_BINARY")
    if override:
        return override
    return "libobfuscated.dylib" if platform.system() == "Darwin" else "libobfuscated.dll"


@pytest.fixture(scope="class")
def libobfuscated_setup(ida_database, configure_hexrays, setup_libobfuscated_funcs):
    """Setup fixture for libobfuscated tests - runs once per class."""
    if not idaapi.init_hexrays_plugin():
        pytest.skip("Hex-Rays decompiler plugin not available")
    return ida_database


class TestLibDeobfuscatedDSL:
    """DSL-based tests for libobfuscated deobfuscation.

    These tests demonstrate the data-driven approach where test cases
    are defined as DeobfuscationCase dataclasses.
    """

    binary_name = _get_default_binary()

    @pytest.mark.parametrize("case", LIBOBFUSCATED_CASES, ids=lambda c: c.test_id)
    def test_deobfuscation(
        self,
        case,
        libobfuscated_setup,
        d810_state,
        pseudocode_to_string,
        code_comparator,
        capture_stats,
        load_expected_stats,
    ):
        """Generic deobfuscation test using DSL runner.

        Each case in LIBOBFUSCATED_CASES becomes a separate test.
        """
        run_deobfuscation_test(
            case=case,
            d810_state=d810_state,
            pseudocode_to_string=pseudocode_to_string,
            code_comparator=code_comparator,
            capture_stats=capture_stats,
            load_expected_stats=load_expected_stats,
        )


class TestLibDeobfuscatedSmoke:
    """Fast smoke tests for CI.

    Uses a subset of cases that run quickly for CI validation.
    """

    binary_name = _get_default_binary()

    @pytest.mark.parametrize("case", SMOKE_TEST_CASES, ids=lambda c: c.test_id)
    def test_smoke(
        self,
        case,
        libobfuscated_setup,
        d810_state,
        pseudocode_to_string,
        code_comparator,
        capture_stats,
        load_expected_stats,
    ):
        """Quick smoke test using DSL runner."""
        run_deobfuscation_test(
            case=case,
            d810_state=d810_state,
            pseudocode_to_string=pseudocode_to_string,
            code_comparator=code_comparator,
            capture_stats=capture_stats,
            load_expected_stats=load_expected_stats,
        )
