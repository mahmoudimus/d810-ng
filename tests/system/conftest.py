"""Pytest configuration for system tests.

System tests require IDA Pro and test actual decompilation functionality.

This module provides:
- IDA Pro initialization and module loading
- libclang initialization for AST-based code comparison
- Pytest fixtures for database management and code comparison

Fixtures defined here are automatically available to all tests - do NOT import
from this file. Pytest auto-injects fixtures by name.

AST-Based Code Comparison
=========================
The CodeComparator class provides structural/semantic code comparison using
libclang, which is more reliable than string comparison because it ignores:
- Formatting differences (indentation, spacing)
- Type name variations (`int` vs `_DWORD`)
- Comment differences (IDA annotations)

Key Fixtures:
- `clang_index`: Session-scoped clang Index (or None if unavailable)
- `code_comparator`: Session-scoped CodeComparator instance
- `require_clang`: Skips test if clang is not available
- `ida_database`: Class-scoped IDA database management
- `assert_code_equivalent`: AST-based equivalence assertion
- `assert_code_contains`: Pattern-based containment assertion
- `assert_code_not_contains`: Pattern-based exclusion assertion
"""

from __future__ import annotations

import contextlib
import logging
import os
import pathlib
import shutil
import sys
import tempfile
import time
import warnings
from typing import TYPE_CHECKING

import pytest

logger = logging.getLogger(__name__)


# =============================================================================
# IDA Pro Initialization
# =============================================================================
def is_ida():
    exec_name = pathlib.Path(sys.executable).name.lower()
    """Crude check to see if running inside IDA."""
    return exec_name.startswith("ida") or exec_name.startswith("idat")


# Try to import idapro first to initialize IDA Python environment
# This is CRITICAL for headless/idalib mode, but not needed if we
# are in the IDA Pro environment.
# See: https://docs.hex-rays.com/user-guide/idalib#using-the-ida-library-python-module

if not is_ida():
    try:
        import idapro
    except ImportError:
        pytest.skip(
            "Not running inside IDA Pro and idapro module not available! Not possible to run system tests."
        )

    print("  idapro module initialized")


# Try to import IDA modules to check availability
with warnings.catch_warnings():
    warnings.filterwarnings("ignore")
    import idaapi
    import idc

print(f"  IDA Pro version: {idaapi.get_kernel_version()}")

# Load all d810 modules to populate registries using reload_package

if TYPE_CHECKING:
    from d810.manager import D810State

import d810
import d810._vendor.ida_reloader as reloadable

# Just scan/import modules to populate registries - no reload needed for tests
reloadable.Scanner.scan(d810.__path__, "d810.", skip_packages=False)
print("  d810 modules loaded")


# =============================================================================
# Pytest Fixtures - Basic
# =============================================================================


@pytest.fixture
def ida_available():
    """Fixture that provides IDA availability status."""
    return True


@pytest.fixture
def skip_if_no_ida():
    """Fixture that skips test if IDA is not available."""
    pytest.skip("IDA Pro not available")


# =============================================================================
# Pytest Fixtures - IDA Database
# =============================================================================


@pytest.fixture(scope="class")
def ida_database(request):
    """Class-scoped fixture for IDA database management.

    Opens the database specified by the test class's `binary_name` attribute.
    """
    binary_name = getattr(request.cls, "binary_name", None)
    if binary_name is None:
        pytest.skip("Test class must set binary_name attribute")

    timing_data = {}

    # Check if the expected database is already open
    try:
        current_db = idaapi.get_root_filename()
        if current_db and (
            binary_name in current_db or current_db.endswith(binary_name)
        ):
            print(f"    Reusing existing database: {current_db}")
            yield {
                "min_ea": idaapi.inf_get_min_ea(),
                "max_ea": idaapi.inf_get_max_ea(),
                "binary_name": binary_name,
                "reused": True,
            }
            return
    except Exception:
        pass

    # Find the binary
    tests_dir = pathlib.Path(__file__).parent
    project_root = tests_dir.parent.parent

    possible_paths = [
        project_root / "samples" / "bins" / binary_name,
        project_root / "tests" / "_resources" / "bin" / binary_name,
        tests_dir / "bins" / binary_name,
    ]

    binary_path = None
    for path in possible_paths:
        if path.exists():
            binary_path = path
            break

    if binary_path is None:
        pytest.skip(f"Test binary '{binary_name}' not found")

    logger.info(f"Found binary at: {binary_path}")

    # Create temporary directory and copy binary
    tempdir = pathlib.Path(tempfile.mkdtemp())
    temp_binary_path = tempdir / binary_path.name
    shutil.copy(binary_path, temp_binary_path)

    logger.info(f"Copied binary to temp location: {temp_binary_path}")

    # Open database
    t_db_start = time.perf_counter()
    result = idapro.open_database(str(temp_binary_path), True)
    timing_data["db_open"] = time.perf_counter() - t_db_start
    print(f"    idapro.open_database() took {timing_data['db_open']:.2f}s")

    if result != 0:
        shutil.rmtree(tempdir)
        pytest.skip(f"Failed to open database. Result code: {result}")

    # Run auto analysis
    t_auto_start = time.perf_counter()
    idaapi.auto_wait()
    timing_data["auto_wait"] = time.perf_counter() - t_auto_start
    print(f"    idaapi.auto_wait() took {timing_data['auto_wait']:.2f}s")

    db_info = {
        "min_ea": idaapi.inf_get_min_ea(),
        "max_ea": idaapi.inf_get_max_ea(),
        "binary_name": binary_name,
        "binary_path": binary_path,
        "temp_path": temp_binary_path,
        "tempdir": tempdir,
        "timing": timing_data,
        "reused": False,
    }

    yield db_info

    # Cleanup
    if not db_info.get("reused", False):
        logger.debug("Closing database...")
        idapro.close_database()
        if tempdir.exists():
            logger.debug("Cleaning up temporary directory...")
            shutil.rmtree(tempdir)


# =============================================================================
# Pytest Fixtures - Hex-Rays Helpers
# =============================================================================


def _pseudocode_to_string(pseudo_code) -> str:
    """Convert IDA pseudocode to a plain string without formatting tags."""
    converted_obj = [idaapi.tag_remove(line_obj.line) for line_obj in pseudo_code]
    return os.linesep.join(converted_obj)


def _configure_hexrays():
    """Configure Hex-Rays decompiler settings for consistent test output."""
    idaapi.change_hexrays_config("RIGHT_MARGIN = 100")
    idaapi.change_hexrays_config("PSEUDOCODE_SYNCED = YES")
    idaapi.change_hexrays_config("PSEUDOCODE_DOCKPOS = DP_RIGHT")
    idaapi.change_hexrays_config("GENERATE_EMPTY_LINES = YES")
    idaapi.change_hexrays_config("BLOCK_INDENT = 4")
    idaapi.change_hexrays_config("MAX_FUNCSIZE = 2048")
    idaapi.change_hexrays_config("MAX_NCOMMAS = 1")
    idaapi.change_hexrays_config("COLLAPSE_LVARS = YES")
    idaapi.change_hexrays_config("GENERATE_EA_LABELS = YES")
    idaapi.change_hexrays_config("AUTO_UNHIDE = YES")
    idaapi.change_hexrays_config("DEFAULT_RADIX = 16")


def _setup_libobfuscated_function_names():
    """Set up function names for libobfuscated.dll."""
    function_map = {
        "constant_folding_test1": 0x180001000,
        "constant_folding_test2": 0x1800015C0,
        "outlined_helper_1": 0x1800016A0,
        "outlined_helper_2": 0x1800016D0,
        "AntiDebug_ExceptionFilter": 0x180001710,
        "test_chained_add": 0x180006630,
        "test_cst_simplification": 0x180006680,
        "test_opaque_predicate": 0x180006780,
        "test_xor": 0x180006920,
        "test_mba_guessing": 0x1800069A0,
        "test_function_ollvm_fla_bcf_sub": 0x180006B40,
        "tigress_minmaxarray": 0x180009490,
        "unwrap_loops": 0x180009730,
        "unwrap_loops_2": 0x1800097E0,
        "unwrap_loops_3": 0x1800098C0,
        "while_switch_flattened": 0x1800099F0,
        "NtCurrentTeb": 0x180009B30,
    }
    for name, addr in function_map.items():
        idc.set_name(addr, name, idc.SN_NOWARN | idc.SN_NOCHECK)
        if not idc.get_func_attr(addr, idc.FUNCATTR_START):
            idc.create_insn(addr)
            idaapi.add_func(addr)


@pytest.fixture
def pseudocode_to_string():
    """Fixture providing the pseudocode_to_string function."""
    return _pseudocode_to_string


@pytest.fixture(scope="class")
def configure_hexrays():
    """Fixture that configures Hex-Rays for consistent output."""
    _configure_hexrays()


@pytest.fixture(scope="class")
def setup_libobfuscated_funcs():
    """Fixture that sets up function names for libobfuscated.dll."""
    _setup_libobfuscated_function_names()


# =============================================================================
# Pytest Fixtures - D810 State
# =============================================================================


@contextlib.contextmanager
def _d810_state_cm(*, all_rules=False):
    """Context manager for D810 state with statistics tracking."""
    from d810.manager import D810State

    state = D810State()  # singleton
    if not (was_loaded := state.is_loaded()):
        t_load_start = time.perf_counter()
        state.load(gui=False)
        t_load = time.perf_counter() - t_load_start
        print(f"    D810State.load() took {t_load:.2f}s")

    if all_rules:
        state.current_ins_rules = state.known_ins_rules
        state.current_blk_rules = state.known_blk_rules
        logger.debug(
            f"all_rules=True: Loaded {len(state.current_ins_rules)} instruction rules"
        )

    if not (was_started := state.manager.started):
        t_start = time.perf_counter()
        state.start_d810()
        t_start_elapsed = time.perf_counter() - t_start
        print(f"    D810State.start_d810() took {t_start_elapsed:.2f}s")

    state.stats.reset()

    try:
        yield state
    finally:
        if not was_started:
            state.stop_d810()
        if not was_loaded:
            state.unload(gui=False)


@pytest.fixture
def d810_state():
    """Fixture providing d810 state context manager.

    Usage:
        def test_something(self, d810_state):
            with d810_state() as state:
                state.stop_d810()
                # decompile without d810
                state.start_d810()
                # decompile with d810
    """
    return _d810_state_cm


@pytest.fixture
def d810_state_all_rules():
    """Fixture providing d810 state with all rules enabled.

    Usage:
        def test_something(self, d810_state_all_rules):
            with d810_state_all_rules() as state:
                # all rules are active
    """
    return lambda: _d810_state_cm(all_rules=True)


# =============================================================================
# Custom Assertion Fixtures
# =============================================================================


@pytest.fixture
def assert_code_contains():
    """Fixture providing code contains assertion."""

    def _assert(actual: str, *expected_patterns: str, msg: str = ""):
        missing = [p for p in expected_patterns if p not in actual]
        if missing:
            fail_msg = (
                f"Code missing expected patterns: {missing}\n\nActual code:\n{actual}"
            )
            if msg:
                fail_msg = f"{msg}\n\n{fail_msg}"
            pytest.fail(fail_msg)

    return _assert


@pytest.fixture
def assert_code_not_contains():
    """Fixture providing code not-contains assertion."""

    def _assert(actual: str, *forbidden_patterns: str, msg: str = ""):
        found = [p for p in forbidden_patterns if p in actual]
        if found:
            fail_msg = (
                f"Code contains forbidden patterns: {found}\n\nActual code:\n{actual}"
            )
            if msg:
                fail_msg = f"{msg}\n\n{fail_msg}"
            pytest.fail(fail_msg)

    return _assert
