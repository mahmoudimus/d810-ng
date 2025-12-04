#!/usr/bin/env python3
"""Run abc_f6_or_dispatch test and capture output."""

import subprocess
import sys
import os

# Set up environment
os.chdir('/Users/mahmoud/src/idapro/d810-ng')
env = os.environ.copy()
env['PYTHONPATH'] = 'src'

# Run the test
cmd = [
    sys.executable, '-m', 'pytest',
    'tests/system/test_unflattening_characterization.py::test_abc_f6_or_dispatch',
    '-v', '-s'
]

print(f"Running: {' '.join(cmd)}")
print(f"PYTHONPATH={env['PYTHONPATH']}")
print("-" * 80)

result = subprocess.run(cmd, env=env, capture_output=True, text=True)

print(result.stdout)
if result.stderr:
    print("STDERR:", file=sys.stderr)
    print(result.stderr, file=sys.stderr)

sys.exit(result.returncode)
