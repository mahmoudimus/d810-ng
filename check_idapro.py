#!/usr/bin/env python3
"""Check if idapro module is available for headless testing."""

import sys
import os

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'src'))

print("Checking for idapro module (idalib)...")
print()

try:
    import idapro
    print("SUCCESS: idapro module is available!")
    print(f"  Module path: {idapro.__file__ if hasattr(idapro, '__file__') else 'built-in'}")

    # Try to check version
    if hasattr(idapro, '__version__'):
        print(f"  Version: {idapro.__version__}")

    print()
    print("Headless testing should work!")
    sys.exit(0)

except ImportError as e:
    print(f"FAILED: idapro module not found: {e}")
    print()
    print("To run tests headlessly, you need:")
    print("1. IDA Pro installed with idalib")
    print("2. Python bindings for idalib installed")
    print("3. Proper IDA_HOME or IDADIR environment variable")
    print()
    print("Without idapro module, tests can only run inside IDA Pro GUI.")
    sys.exit(1)