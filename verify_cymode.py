#!/usr/bin/env python3
"""Verification script to demonstrate CythonMode functionality.

Run this script with and without D810_NO_CYTHON=1 to verify the import pattern.
"""

import sys
import os

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'src'))

from d810.core.cymode import CythonMode

print("=" * 60)
print("CythonMode Verification Script")
print("=" * 60)

# Check environment variable
env_var = os.environ.get("D810_NO_CYTHON", "not set")
print(f"D810_NO_CYTHON environment variable: {env_var}")

# Check CythonMode state
mode = CythonMode()
print(f"CythonMode.is_enabled(): {mode.is_enabled()}")

print("\n" + "=" * 60)
print("Testing module imports...")
print("=" * 60)

# Test block_helpers
try:
    from d810.hexrays import block_helpers
    print(f"✓ block_helpers._CYTHON_AVAILABLE: {block_helpers._CYTHON_AVAILABLE}")
except Exception as e:
    print(f"✗ block_helpers import failed: {e}")

# Test hexrays_helpers
try:
    from d810.hexrays import hexrays_helpers
    print(f"✓ hexrays_helpers.cy_hash_mop: {hexrays_helpers.cy_hash_mop}")
except Exception as e:
    print(f"✗ hexrays_helpers import failed: {e}")

# Test tracker_components
try:
    from d810.hexrays import tracker_components
    print(f"✓ tracker_components imported successfully")
except Exception as e:
    print(f"✗ tracker_components import failed: {e}")

print("\n" + "=" * 60)
print("Summary")
print("=" * 60)

if mode.is_enabled():
    print("✓ CythonMode is ENABLED")
    print("  Cython speedups will be used if available")
    print("  To disable: export D810_NO_CYTHON=1")
else:
    print("✓ CythonMode is DISABLED")
    print("  Pure Python implementations will be used")
    print("  To enable: unset D810_NO_CYTHON or set it to 0")

print("=" * 60)
