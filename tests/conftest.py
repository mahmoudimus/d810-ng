"""Pytest configuration for d810-ng tests.

Shared configuration for all test suites.
"""

import sys
from pathlib import Path

# Add project root to path for all tests
project_root = Path(__file__).parent.parent
sys.path.insert(0, str(project_root / "src"))
sys.path.insert(0, str(project_root / "tests"))


def pytest_configure(config):
    """Configure pytest with custom markers."""
    config.addinivalue_line(
        "markers", "ida_required: mark test as requiring IDA Pro"
    )
    config.addinivalue_line(
        "markers", "integration: mark test as integration test"
    )
