#!/usr/bin/env python3
"""
Example usage of structured logging to verify implementation.
"""

import logging
import sys
import os

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'src'))

from d810.core.structured_logging import debug_scope, query_logs

def main():
    """Run example usage."""
    print("Testing SQLite structured logging...")

    # Get a logger
    logger = logging.getLogger('d810.test')

    # Use debug scope
    db_path = '/tmp/test_debug.db'

    with debug_scope(
        loggers='d810.test',
        db_path=db_path,
        test_id='my_test'
    ) as handler:
        print(f"Created handler with db_path: {handler.db_path}")
        logger.debug("Debug message", extra={'custom_field': 'value'})
        logger.info("Info message")
        logger.warning("Warning with data", extra={'histories': [1, 2, 3]})

    # Query the logs
    print(f"\nQuerying logs from {db_path}...")
    logs = query_logs(db_path, test_id='my_test')

    print(f"Found {len(logs)} log entries:")
    for log in logs:
        print(f"  {log['level']:8s}: {log['message']}")
        if log.get('extra'):
            print(f"    Extra: {log['extra']}")

    # Query specific level
    print("\nDebug logs only:")
    debug_logs = query_logs(db_path, test_id='my_test', level='DEBUG')
    for log in debug_logs:
        print(f"  {log['message']}")

    print("\nTest completed successfully!")

if __name__ == '__main__':
    main()