#!/usr/bin/env python
"""
Investigation script for d810ng-symex-01.
Runs abc_f6_or_dispatch deobfuscation with structured logging.
"""
import sys
import os
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent / 'src'))

DB_PATH = '/tmp/symex_investigation.db'
TEST_ID = 'abc_f6_or_dispatch_investigation'

def main():
    """
    Main investigation entry point.
    This needs to be integrated with the IDA Pro test environment.
    """
    print(f"Investigation DB: {DB_PATH}")
    print(f"Test ID: {TEST_ID}")
    print()

    # Check if we can import structured logging
    try:
        from d810.core.structured_logging import debug_scope, query_logs
        print("✓ Structured logging available")
    except ImportError as e:
        print(f"✗ Cannot import structured logging: {e}")
        return 1

    print("\nTo run with debug logging:")
    print("1. Modify test to use debug_scope")
    print("2. Run: PYTHONPATH=src pytest tests/system/cases/libobfuscated_comprehensive.py \\")
    print("        -k 'abc_f6_or_dispatch' -v --tb=long")
    print()
    print("Alternatively, instrument UnflattenerFakeJump directly.")

    return 0

if __name__ == '__main__':
    sys.exit(main())