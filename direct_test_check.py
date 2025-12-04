#!/usr/bin/env python3
"""Direct test verification without needing IDA Pro."""

import sys
import os

# Add src to path
sys.path.insert(0, '/Users/mahmoud/src/idapro/d810-ng/src')

print("=" * 70)
print("PYTEST COMMAND EXECUTION REPORT")
print("=" * 70)

print("\nCommand 1: Check if idapro module is available")
print("-" * 70)
try:
    import idapro
    print("SUCCESS: idapro module available")
    print(f"  idapro location: {idapro.__file__}")
except ImportError as e:
    print("FAILED: idapro not available")
    print(f"  Error: {e}")

print("\nCommand 2: Check pytest availability")
print("-" * 70)
try:
    import pytest
    print(f"SUCCESS: pytest available")
    print(f"  pytest version: {pytest.__version__}")
    print(f"  pytest location: {pytest.__file__}")
except ImportError as e:
    print("FAILED: pytest not available")
    print(f"  Error: {e}")

print("\nCommand 3: Check d810 module availability")
print("-" * 70)
try:
    import d810
    print(f"SUCCESS: d810 module available")
    print(f"  d810 location: {d810.__file__}")
except ImportError as e:
    print("FAILED: d810 not available")
    print(f"  Error: {e}")

print("\nCommand 4: Check test case definitions")
print("-" * 70)
try:
    from tests.system.cases.libobfuscated_comprehensive import ABC_F6_CASES
    print(f"SUCCESS: ABC_F6_CASES available")
    print(f"  Number of ABC F6 cases: {len(ABC_F6_CASES)}")

    # Find abc_f6_or_dispatch
    for i, case in enumerate(ABC_F6_CASES):
        if case.function == "abc_f6_or_dispatch":
            print(f"\n  Found abc_f6_or_dispatch (case #{i}):")
            print(f"    Description: {case.description}")
            print(f"    Project: {case.project}")
            print(f"    Expected code present: {case.expected_code is not None}")
            break
except ImportError as e:
    print("FAILED: ABC_F6_CASES not available")
    print(f"  Error: {e}")

print("\nCommand 5: Check test file structure")
print("-" * 70)
test_file_path = "/Users/mahmoud/src/idapro/d810-ng/tests/system/test_libdeobfuscated_dsl.py"
if os.path.exists(test_file_path):
    print(f"SUCCESS: Test file exists at {test_file_path}")
    with open(test_file_path, 'r') as f:
        content = f.read()

    # Count test classes and methods
    import re
    classes = re.findall(r'class (Test\w+)', content)
    print(f"  Test classes found: {len(classes)}")
    for cls in classes:
        print(f"    - {cls}")
else:
    print(f"FAILED: Test file not found at {test_file_path}")

print("\nCommand 6: Pytest collection simulation")
print("-" * 70)
try:
    import subprocess
    env = os.environ.copy()
    env['PYTHONPATH'] = '/Users/mahmoud/src/idapro/d810-ng/src'

    result = subprocess.run(
        [sys.executable, '-m', 'pytest',
         '/Users/mahmoud/src/idapro/d810-ng/tests/system/test_libdeobfuscated_dsl.py',
         '-k', 'abc_f6_or_dispatch',
         '--collect-only', '-q'],
        capture_output=True,
        text=True,
        timeout=10,
        cwd='/Users/mahmoud/src/idapro/d810-ng',
        env=env
    )

    print(f"Return code: {result.returncode}")
    if result.stdout:
        print(f"Output:\n{result.stdout[:1000]}")
    if result.stderr and result.returncode != 0:
        print(f"Errors:\n{result.stderr[:1000]}")

except Exception as e:
    print(f"Could not run pytest: {e}")

print("\n" + "=" * 70)
print("END OF REPORT")
print("=" * 70)
