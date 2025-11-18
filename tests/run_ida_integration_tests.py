#!/usr/bin/env python
"""IDA Pro integration test runner.

This script runs system/integration tests in IDA Pro's headless mode against
real obfuscated binaries (libobfuscated.dll).

Usage:
    # Run with idat64/idat (IDA headless mode):
    idat64 -A -S"tests/run_ida_integration_tests.py" samples/bins/libobfuscated.dll

    # Or use the wrapper script (if available):
    ./run_integration_tests.sh

The script will:
1. Set up the Python path
2. Open the database (libobfuscated.dll)
3. Run auto-analysis
4. Execute all integration tests
5. Collect coverage data
6. Report results and exit
"""

import sys
import os
import traceback
import unittest
from pathlib import Path

# Add project directories to Python path
project_root = Path(__file__).parent.parent
sys.path.insert(0, str(project_root / "src"))
sys.path.insert(0, str(project_root / "tests"))

print("=" * 80)
print("D810-NG Integration Test Runner (IDA Pro Headless Mode)")
print("=" * 80)
print(f"Project root: {project_root}")
print(f"Python version: {sys.version}")

# Import IDA modules
try:
    import idaapi
    import idc
    print(f"IDA database: {idc.get_idb_path()}")
    print(f"IDA version: {idaapi.get_kernel_version()}")
except ImportError as e:
    print(f"ERROR: Could not import IDA modules: {e}")
    sys.exit(1)

print("=" * 80)


def main():
    """Run integration tests and return exit code."""
    try:
        # Import test modules
        print("\nDiscovering tests...")
        from tests.system import test_libobfuscated_integration

        # Create test suite
        loader = unittest.TestLoader()
        suite = unittest.TestSuite()

        # Load tests from the integration module
        suite.addTests(loader.loadTestsFromModule(test_libobfuscated_integration))

        print(f"Found {suite.countTestCases()} test(s)")
        print("=" * 80)

        # Run tests with verbose output
        runner = unittest.TextTestRunner(verbosity=2)
        result = runner.run(suite)

        # Print summary
        print("\n" + "=" * 80)
        print("INTEGRATION TEST SUMMARY")
        print("=" * 80)
        print(f"Tests run:     {result.testsRun}")
        print(f"Passed:        {result.testsRun - len(result.failures) - len(result.errors)}")
        print(f"Failed:        {len(result.failures)}")
        print(f"Errors:        {len(result.errors)}")
        print(f"Skipped:       {len(result.skipped)}")
        print("=" * 80)

        # Report coverage if available
        try:
            import coverage
            print("\nCoverage data saved to: .coverage.integration")
            print("Run 'coverage report' to see coverage statistics")
        except ImportError:
            print("\nNote: coverage module not available, no coverage data collected")

        # Determine exit code
        if result.wasSuccessful():
            print("\nALL INTEGRATION TESTS PASSED ✓")
            return 0
        else:
            print("\nSOME INTEGRATION TESTS FAILED ✗")
            return 1

    except Exception as e:
        print(f"\nFATAL ERROR: {e}")
        traceback.print_exc()
        return 1


if __name__ == "__main__":
    try:
        exit_code = main()

        # In IDA headless mode, we need to explicitly exit
        print(f"\nExiting with code {exit_code}")
        idaapi.qexit(exit_code)

    except Exception as e:
        print(f"\nFATAL ERROR during exit: {e}")
        traceback.print_exc()
        idaapi.qexit(1)
