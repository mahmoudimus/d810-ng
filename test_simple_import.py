#!/usr/bin/env python3
"""
Simple test to check if we can import test modules and run abc test.
"""

import sys
import os
from pathlib import Path

# Add src to path
repo_root = Path(__file__).parent
sys.path.insert(0, str(repo_root / 'src'))

print("=" * 80)
print("SIMPLE ABC TEST IMPORT CHECK")
print("=" * 80)
print()

# Step 1: Check basic imports
print("1. Checking basic imports...")
try:
    import d810
    print("   ✓ d810 module imported")
except ImportError as e:
    print(f"   ✗ Cannot import d810: {e}")
    sys.exit(1)

# Step 2: Check testing module
print("\n2. Checking testing module...")
try:
    from d810.testing import DeobfuscationCase, run_deobfuscation_test
    print("   ✓ Testing framework imported")
except ImportError as e:
    print(f"   ✗ Cannot import testing: {e}")
    sys.exit(1)

# Step 3: Check test cases
print("\n3. Loading test cases...")
try:
    from tests.system.cases.libobfuscated_comprehensive import ABC_F6_CASES
    print(f"   ✓ Loaded {len(ABC_F6_CASES)} ABC_F6 test cases")

    # Find abc_f6_or_dispatch
    abc_or_case = None
    for case in ABC_F6_CASES:
        if case.function == "abc_f6_or_dispatch":
            abc_or_case = case
            break

    if abc_or_case:
        print(f"   ✓ Found abc_f6_or_dispatch test case")
        print(f"      Description: {abc_or_case.description}")
        print(f"      Project: {abc_or_case.project}")
        print(f"      Required rules: {abc_or_case.required_rules}")
        if abc_or_case.expected_code:
            lines = abc_or_case.expected_code.strip().split('\n')
            print(f"      Expected output:")
            for line in lines[:3]:
                print(f"        {line}")
    else:
        print("   ✗ abc_f6_or_dispatch not found in test cases")

except ImportError as e:
    print(f"   ✗ Cannot import test cases: {e}")
    sys.exit(1)

# Step 4: Check IDA availability
print("\n4. Checking IDA availability...")

# Check if in IDA
try:
    import ida_kernwin
    print("   ✓ Running inside IDA Pro - tests can run")
    can_run = True
except ImportError:
    print("   ⊘ Not running inside IDA Pro")
    can_run = False

# Check for headless mode
if not can_run:
    try:
        import idapro
        print("   ✓ idapro module available - headless testing possible")
        can_run = True
    except ImportError:
        print("   ⊘ idapro module not available - headless testing not possible")

print("\n" + "=" * 80)
print("SUMMARY")
print("=" * 80)

if can_run:
    print("✓ All prerequisites met - test CAN be run")
    print("\nTo run the test:")
    print("  cd /Users/mahmoud/src/idapro/d810-ng")
    print("  PYTHONPATH=src python -m pytest \\")
    print("    tests/system/test_libdeobfuscated_dsl.py::TestABCPatterns::test_abc_patterns[abc_f6_or_dispatch] \\")
    print("    -v -s")
else:
    print("✗ Cannot run test without IDA")
    print("\nOptions:")
    print("1. Install IDA Pro with idalib for headless testing")
    print("2. Run this script inside IDA Pro")
    print("3. Use: ida64 -B -S'test_simple_import.py' samples/bin/libobfuscated.dll")

sys.exit(0 if can_run else 1)