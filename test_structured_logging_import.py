#!/usr/bin/env python
"""Quick test to verify structured_logging imports."""
import sys
import os
sys.path.insert(0, 'src')

try:
    from d810.core.structured_logging import debug_scope, query_logs
    print('✓ Import OK')
    print(f'  debug_scope: {debug_scope}')
    print(f'  query_logs: {query_logs}')
except ImportError as e:
    print(f'✗ Import failed: {e}')
    sys.exit(1)