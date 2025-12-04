#!/usr/bin/env python3
"""Check pytest availability and run tests."""

import subprocess
import sys
import os

os.chdir('/Users/mahmoud/src/idapro/d810-ng')

print("=" * 50)
print("COMMAND 1: Check idapro module")
print("=" * 50)
try:
    result = subprocess.run(
        [sys.executable, '-c', 'import idapro; print("SUCCESS: idapro module available")'],
        capture_output=True,
        text=True,
        timeout=5
    )
    if result.returncode == 0:
        print(result.stdout)
    else:
        print("FAILED: idapro not available")
        print(f"stderr: {result.stderr}")
except Exception as e:
    print(f"Exception: {e}")

print()
print("=" * 50)
print("COMMAND 2: Check pytest availability")
print("=" * 50)
try:
    result = subprocess.run(
        [sys.executable, '-m', 'pytest', '--version'],
        capture_output=True,
        text=True,
        timeout=5
    )
    print(result.stdout)
    if result.stderr:
        print(f"stderr: {result.stderr}")
except Exception as e:
    print(f"Exception: {e}")

print()
print("=" * 50)
print("COMMAND 3: Collect tests from test_structured_logging.py")
print("=" * 50)
try:
    env = os.environ.copy()
    env['PYTHONPATH'] = 'src'
    result = subprocess.run(
        [sys.executable, '-m', 'pytest',
         'tests/unit/core/test_structured_logging.py',
         '--collect-only'],
        capture_output=True,
        text=True,
        timeout=10,
        env=env
    )
    lines = result.stdout.split('\n')[:50]
    print('\n'.join(lines))
    if result.stderr:
        print(f"stderr: {result.stderr[:500]}")
except Exception as e:
    print(f"Exception: {e}")

print()
print("=" * 50)
print("COMMAND 4: Run test_structured_logging.py tests")
print("=" * 50)
try:
    env = os.environ.copy()
    env['PYTHONPATH'] = 'src'
    result = subprocess.run(
        [sys.executable, '-m', 'pytest',
         'tests/unit/core/test_structured_logging.py',
         '-v'],
        capture_output=True,
        text=True,
        timeout=30,
        env=env
    )
    lines = result.stdout.split('\n')[:100]
    print('\n'.join(lines))
    if result.returncode != 0 and result.stderr:
        print(f"\nstderr (first 500 chars): {result.stderr[:500]}")
except Exception as e:
    print(f"Exception: {e}")

print()
print("=" * 50)
print("COMMAND 5: Check for abc_f6_or_dispatch test")
print("=" * 50)
try:
    env = os.environ.copy()
    env['PYTHONPATH'] = 'src'
    result = subprocess.run(
        [sys.executable, '-m', 'pytest',
         'tests/system/test_libdeobfuscated_dsl.py',
         '-k', 'abc_f6_or_dispatch',
         '--collect-only'],
        capture_output=True,
        text=True,
        timeout=10,
        env=env
    )
    print(result.stdout[:500])
    if result.stderr:
        print(f"stderr: {result.stderr[:500]}")
except Exception as e:
    print(f"Exception: {e}")
