#!/usr/bin/env python3
"""
Comprehensive test runner for abc_f6_or_dispatch.
Reports actual test status and captures deobfuscated output.
"""

import os
import sys
import subprocess
import json
from pathlib import Path

def check_prerequisites():
    """Check if we can run the test."""
    print("=== Checking Prerequisites ===\n")

    # Check for idapro module
    try:
        import idapro
        print("✓ idapro module available (headless testing possible)")
        return True
    except ImportError:
        print("✗ idapro module not found")

    # Check if running in IDA
    try:
        import ida_kernwin
        print("✓ Running inside IDA Pro")
        return True
    except ImportError:
        print("✗ Not running inside IDA Pro")

    return False

def run_pytest_test():
    """Try to run the test via pytest."""
    print("\n=== Running Test via pytest ===\n")

    repo_root = Path(__file__).parent
    os.chdir(repo_root)

    env = os.environ.copy()
    env['PYTHONPATH'] = str(repo_root / 'src')

    cmd = [
        sys.executable, '-m', 'pytest',
        'tests/system/test_libdeobfuscated_dsl.py::TestABCPatterns::test_abc_patterns[abc_f6_or_dispatch]',
        '-v', '-s', '--tb=line',
        '--capture=no'
    ]

    print(f"Command: {' '.join(cmd)}")
    print(f"Working dir: {os.getcwd()}")
    print(f"PYTHONPATH: {env['PYTHONPATH']}")
    print()

    result = subprocess.run(
        cmd,
        env=env,
        capture_output=True,
        text=True
    )

    return result

def extract_test_info(output):
    """Extract key information from test output."""
    info = {
        'passed': False,
        'failed': False,
        'skipped': False,
        'error': None,
        'deobfuscated_code': None,
        'rules_fired': [],
        'moptracker_info': []
    }

    lines = output.split('\n')
    for i, line in enumerate(lines):
        # Check test result
        if 'PASSED' in line:
            info['passed'] = True
        elif 'FAILED' in line:
            info['failed'] = True
        elif 'SKIPPED' in line or 'SKIP' in line:
            info['skipped'] = True

        # Look for deobfuscated code
        if 'Deobfuscated:' in line or 'deobfuscated_code' in line:
            # Try to extract the next few lines
            for j in range(i+1, min(i+20, len(lines))):
                if lines[j].strip():
                    if info['deobfuscated_code'] is None:
                        info['deobfuscated_code'] = []
                    info['deobfuscated_code'].append(lines[j])

        # Look for rules fired
        if 'Rule fired:' in line or 'UnflattenerFakeJump' in line:
            info['rules_fired'].append(line.strip())

        # Look for MopTracker info
        if 'MopTracker' in line or 'history' in line.lower() or '0xF6' in line:
            info['moptracker_info'].append(line.strip())

        # Capture errors
        if 'AssertionError' in line or 'Error:' in line:
            if info['error'] is None:
                info['error'] = line.strip()

    return info

def main():
    """Main test runner."""
    print("=" * 80)
    print("ABC_F6_OR_DISPATCH TEST RUNNER")
    print("=" * 80)
    print()

    # Step 1: Check prerequisites
    can_run = check_prerequisites()

    if not can_run:
        print("\nCannot run test - missing prerequisites")
        print("\nTo run headlessly, you need:")
        print("1. IDA Pro with idalib installed")
        print("2. idapro Python module available")
        print("3. Or run this script inside IDA Pro")
        return 1

    # Step 2: Run the test
    result = run_pytest_test()

    print("\n=== Test Results ===\n")

    # Parse output
    all_output = result.stdout + '\n' + result.stderr
    info = extract_test_info(all_output)

    # Report results
    print(f"Exit Code: {result.returncode}")

    if info['passed']:
        print("Status: PASSED ✓")
    elif info['failed']:
        print("Status: FAILED ✗")
    elif info['skipped']:
        print("Status: SKIPPED ⊘")
    else:
        print("Status: UNKNOWN")

    if info['error']:
        print(f"\nError: {info['error']}")

    if info['deobfuscated_code']:
        print("\nDeobfuscated Code Found:")
        for line in info['deobfuscated_code'][:10]:
            print(f"  {line}")

    if info['rules_fired']:
        print(f"\nRules Fired ({len(info['rules_fired'])}):")
        for rule in info['rules_fired'][:5]:
            print(f"  {rule}")

    if info['moptracker_info']:
        print(f"\nMopTracker Info ({len(info['moptracker_info'])}):")
        for line in info['moptracker_info'][:5]:
            print(f"  {line}")

    # Save full output
    output_file = "test_abc_output.txt"
    with open(output_file, 'w') as f:
        f.write("=== STDOUT ===\n")
        f.write(result.stdout)
        f.write("\n\n=== STDERR ===\n")
        f.write(result.stderr)

    print(f"\nFull output saved to: {output_file}")

    # Summary
    print("\n" + "=" * 80)
    print("SUMMARY")
    print("=" * 80)

    if info['passed']:
        print("✓ Test PASSED - deobfuscation working correctly")
    elif info['failed']:
        print("✗ Test FAILED - deobfuscation not producing expected output")
        print("\nExpected: return a1 | 0xFFu")
        print("Check test_abc_output.txt for actual output")
    elif info['skipped']:
        print("⊘ Test SKIPPED - likely missing IDA/binary")
    else:
        print("? Test status unclear - check test_abc_output.txt")

    return result.returncode

if __name__ == '__main__':
    sys.exit(main())