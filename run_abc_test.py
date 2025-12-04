#!/usr/bin/env python3
"""
Direct test runner for abc_f6_or_dispatch test case.
Tries to run the test and capture all output.
"""
import os
import sys
import subprocess

def main():
    """Run the abc_f6_or_dispatch test."""

    # Set up environment
    repo_root = "/Users/mahmoud/src/idapro/d810-ng"
    os.chdir(repo_root)

    env = os.environ.copy()
    env['PYTHONPATH'] = os.path.join(repo_root, 'src')

    # Command to run
    cmd = [
        sys.executable, '-m', 'pytest',
        'tests/system/test_libdeobfuscated_dsl.py::TestABCPatterns::test_abc_patterns[abc_f6_or_dispatch]',
        '-v', '-s', '--tb=short'
    ]

    print("Running command:")
    print(" ".join(cmd))
    print()
    print("Environment:")
    print(f"  PYTHONPATH={env['PYTHONPATH']}")
    print(f"  Working dir: {os.getcwd()}")
    print()
    print("=" * 80)
    print("Test Output:")
    print("=" * 80)

    try:
        result = subprocess.run(
            cmd,
            env=env,
            capture_output=False,  # Show output directly
            text=True
        )

        print()
        print("=" * 80)
        print(f"Exit code: {result.returncode}")

        return result.returncode

    except Exception as e:
        print(f"Error running test: {e}")
        return 1

if __name__ == '__main__':
    sys.exit(main())