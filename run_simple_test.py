#!/usr/bin/env python3
"""
Simple test runner for structured logging.
"""

import sys
import os
import subprocess

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'src'))

def run_verification():
    """Run the verification script."""
    print("=" * 60)
    print("Running Verification Script")
    print("=" * 60)

    result = subprocess.run(
        [sys.executable, 'verify_structured_logging.py'],
        capture_output=True,
        text=True
    )

    print(result.stdout)
    if result.stderr:
        print("STDERR:", result.stderr)

    return result.returncode == 0

def run_pytest():
    """Run pytest tests."""
    print("\n" + "=" * 60)
    print("Running PyTest Unit Tests")
    print("=" * 60)

    # Set PYTHONPATH
    env = os.environ.copy()
    env['PYTHONPATH'] = os.path.join(os.path.dirname(__file__), 'src')

    result = subprocess.run(
        [sys.executable, '-m', 'pytest',
         'tests/unit/core/test_structured_logging.py',
         '-v', '--tb=short'],
        capture_output=True,
        text=True,
        env=env
    )

    print(result.stdout)
    if result.stderr:
        print("STDERR:", result.stderr)

    return result.returncode == 0

def main():
    """Run all tests."""
    success = True

    # Run verification
    if not run_verification():
        print("\n❌ Verification failed!")
        success = False

    # Run pytest
    if success:
        if not run_pytest():
            print("\n❌ PyTest tests failed!")
            success = False

    if success:
        print("\n" + "=" * 60)
        print("✅ All tests passed successfully!")
        print("=" * 60)

    return 0 if success else 1

if __name__ == '__main__':
    sys.exit(main())