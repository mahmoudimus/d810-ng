#!/usr/bin/env python3
"""
Minimal test to check if SQLiteHandler works.
"""

import sys
import os
import logging
import tempfile

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'src'))

try:
    from d810.core.structured_logging import SQLiteHandler, debug_scope, query_logs
    print("✓ Import successful")

    # Test basic functionality
    with tempfile.NamedTemporaryFile(suffix='.db', delete=False) as f:
        db_path = f.name

    try:
        # Create handler
        handler = SQLiteHandler(db_path, test_id='test1')
        print(f"✓ Handler created with db_path: {db_path}")

        # Create logger
        logger = logging.getLogger('test')
        logger.addHandler(handler)
        logger.setLevel(logging.DEBUG)

        # Log messages
        logger.debug("Debug message")
        logger.info("Info message")
        print("✓ Messages logged")

        # Query logs
        logs = query_logs(db_path, test_id='test1')
        print(f"✓ Found {len(logs)} logs")

        for log in logs:
            print(f"  - {log['level']}: {log['message']}")

        # Test debug_scope
        with debug_scope(loggers='test2', db_path=db_path, test_id='test2'):
            logger2 = logging.getLogger('test2')
            logger2.debug("In scope")

        logs2 = query_logs(db_path, test_id='test2')
        print(f"✓ debug_scope captured {len(logs2)} logs")

        print("\n✅ All basic tests passed!")

    finally:
        # Cleanup
        if os.path.exists(db_path):
            os.unlink(db_path)

except Exception as e:
    print(f"❌ Error: {e}")
    import traceback
    traceback.print_exc()
    sys.exit(1)