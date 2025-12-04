#!/usr/bin/env python3
"""
Run abc_f6_or_dispatch test and capture output to file.
This script attempts to run the test and save all output for analysis.
"""

import os
import sys
import subprocess
from datetime import datetime

def main():
    """Run the test and capture output."""
    repo_root = "/Users/mahmoud/src/idapro/d810-ng"
    os.chdir(repo_root)

    # Prepare output file
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    output_file = f"test_output_{timestamp}.txt"

    print(f"Running abc_f6_or_dispatch test...")
    print(f"Output will be saved to: {output_file}")
    print()

    # Set up environment
    env = os.environ.copy()
    env['PYTHONPATH'] = os.path.join(repo_root, 'src')

    # Try different test approaches
    commands = [
        # Direct pytest
        [
            sys.executable, '-m', 'pytest',
            'tests/system/test_libdeobfuscated_dsl.py::TestABCPatterns::test_abc_patterns[abc_f6_or_dispatch]',
            '-v', '-s', '--tb=short'
        ],
        # With debug flag
        [
            sys.executable, '-m', 'pytest',
            'tests/system/test_libdeobfuscated_dsl.py::TestABCPatterns::test_abc_patterns[abc_f6_or_dispatch]',
            '-v', '-s', '--tb=long', '--capture=no'
        ],
    ]

    with open(output_file, 'w') as f:
        f.write(f"Test run at: {datetime.now()}\n")
        f.write(f"Working directory: {os.getcwd()}\n")
        f.write(f"PYTHONPATH: {env.get('PYTHONPATH', 'not set')}\n")
        f.write("=" * 80 + "\n\n")

        for i, cmd in enumerate(commands, 1):
            print(f"Attempt {i}: {' '.join(cmd[:4])}...")
            f.write(f"Attempt {i}: {' '.join(cmd)}\n")
            f.write("-" * 80 + "\n")

            try:
                result = subprocess.run(
                    cmd,
                    env=env,
                    capture_output=True,
                    text=True,
                    timeout=60  # 60 second timeout
                )

                f.write("STDOUT:\n")
                f.write(result.stdout)
                f.write("\n\nSTDERR:\n")
                f.write(result.stderr)
                f.write(f"\n\nExit code: {result.returncode}\n")
                f.write("=" * 80 + "\n\n")

                if result.returncode == 0:
                    print(f"  SUCCESS! Test passed.")
                else:
                    print(f"  FAILED with exit code {result.returncode}")

                # Print first 50 lines to console
                lines = result.stdout.split('\n')
                for line in lines[:50]:
                    print(line)
                if len(lines) > 50:
                    print(f"... ({len(lines) - 50} more lines in {output_file})")

            except subprocess.TimeoutExpired:
                print(f"  TIMEOUT after 60 seconds")
                f.write("TIMEOUT: Process killed after 60 seconds\n")
                f.write("=" * 80 + "\n\n")
            except Exception as e:
                print(f"  ERROR: {e}")
                f.write(f"ERROR: {e}\n")
                f.write("=" * 80 + "\n\n")

    print()
    print(f"Full output saved to: {output_file}")
    print()
    print("To view: cat", output_file)
    return 0

if __name__ == '__main__':
    sys.exit(main())