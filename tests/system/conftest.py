"""Pytest configuration for system tests.

System tests require IDA Pro and test actual decompilation functionality.
"""

import pytest

# Try to import idapro first to initialize IDA Python environment
# This is CRITICAL for headless/idalib mode
try:
    import idapro
    print("✓ idapro module initialized")
except ImportError:
    # idapro not available - likely running outside IDA environment
    # Tests will be skipped
    pass

# Try to import IDA modules to check availability
try:
    import idaapi
    IDA_AVAILABLE = True
    print(f"✓ IDA Pro available: {idaapi.get_kernel_version()}")
except ImportError:
    IDA_AVAILABLE = False
    print("⚠ IDA Pro not available - system tests will be skipped")


def pytest_collection_modifyitems(config, items):
    """Skip system tests if IDA is not available."""
    if IDA_AVAILABLE:
        return

    skip_ida = pytest.mark.skip(reason="IDA Pro not available")
    for item in items:
        # All items in this directory require IDA
        item.add_marker(skip_ida)


@pytest.fixture
def ida_available():
    """Fixture that provides IDA availability status."""
    return IDA_AVAILABLE


@pytest.fixture
def skip_if_no_ida():
    """Fixture that skips test if IDA is not available."""
    if not IDA_AVAILABLE:
        pytest.skip("IDA Pro not available")
