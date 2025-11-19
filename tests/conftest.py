"""Pytest configuration for d810-ng tests.

This conftest ensures IDA Pro modules are available before test collection.
"""

import sys
import os
from pathlib import Path

# Add project root to path
project_root = Path(__file__).parent.parent
sys.path.insert(0, str(project_root / "src"))
sys.path.insert(0, str(project_root / "tests"))

# Try to import IDA modules early to ensure they're available
try:
    import idaapi
    IDA_AVAILABLE = True
    print(f"✓ IDA Pro available: {idaapi.get_kernel_version()}")
except ImportError:
    IDA_AVAILABLE = False
    print("⚠ IDA Pro not available - only non-IDA tests will run")


def pytest_configure(config):
    """Configure pytest with custom markers."""
    config.addinivalue_line(
        "markers", "ida_required: mark test as requiring IDA Pro"
    )
    config.addinivalue_line(
        "markers", "integration: mark test as integration test"
    )


def pytest_collection_modifyitems(config, items):
    """Skip tests that require IDA if IDA is not available."""
    if IDA_AVAILABLE:
        return

    skip_ida = pytest.mark.skip(reason="IDA Pro not available")
    for item in items:
        if "system" in str(item.fspath) or "integration" in str(item.fspath):
            item.add_marker(skip_ida)
