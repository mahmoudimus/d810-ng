#!/usr/bin/env python
"""Test runner for structured_logging tests."""
import subprocess
import sys
import os

os.chdir('/Users/mahmoud/src/idapro/d810-ng')
env = os.environ.copy()
env['PYTHONPATH'] = 'src'

result = subprocess.run(
    [sys.executable, '-m', 'pytest',
     'tests/unit/core/test_structured_logging.py',
     '-v', '--tb=short'],
    env=env,
    capture_output=True,
    text=True
)

print(result.stdout)
print(result.stderr)
sys.exit(result.returncode)
