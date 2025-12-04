#!/usr/bin/env python3
"""
Quick verification script for structured logging implementation.
"""

import sys
import os
import tempfile
import json

# Add src to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'src'))

def test_basic_functionality():
    """Test basic SQLite handler functionality."""
    import logging
    from d810.core.structured_logging import SQLiteHandler, debug_scope, query_logs

    print("=" * 60)
    print("Testing Basic SQLite Handler Functionality")
    print("=" * 60)

    with tempfile.NamedTemporaryFile(suffix='.db', delete=False) as f:
        db_path = f.name

    try:
        # Test 1: Handler creation and basic logging
        print("\n1. Testing handler creation and basic logging...")
        handler = SQLiteHandler(db_path, test_id='test_run_1')
        logger = logging.getLogger('test.basic')
        logger.addHandler(handler)
        logger.setLevel(logging.DEBUG)

        logger.debug("Debug message")
        logger.info("Info message")
        logger.warning("Warning message")

        # Remove handler
        logger.removeHandler(handler)
        handler.close()

        # Query logs
        logs = query_logs(db_path, test_id='test_run_1')
        print(f"   - Logged {len(logs)} messages")
        assert len(logs) == 3, f"Expected 3 logs, got {len(logs)}"
        print("   ✓ Basic logging works")

        # Test 2: Extra data serialization
        print("\n2. Testing extra data serialization...")
        handler2 = SQLiteHandler(db_path, test_id='test_run_2')
        logger2 = logging.getLogger('test.extra')
        logger2.addHandler(handler2)
        logger2.setLevel(logging.INFO)

        extra_data = {'user_id': 42, 'values': [1, 2, 3]}
        logger2.info("Message with extra", extra=extra_data)

        logger2.removeHandler(handler2)
        handler2.close()

        logs2 = query_logs(db_path, test_id='test_run_2')
        assert len(logs2) == 1
        assert logs2[0]['extra'] is not None
        assert logs2[0]['extra']['user_id'] == 42
        print(f"   - Extra data preserved: {logs2[0]['extra']}")
        print("   ✓ Extra data serialization works")

        # Test 3: debug_scope context manager
        print("\n3. Testing debug_scope context manager...")
        logger3 = logging.getLogger('test.scope')
        original_level = logger3.level

        with debug_scope(
            loggers='test.scope',
            db_path=db_path,
            test_id='test_run_3',
            level=logging.DEBUG
        ):
            assert logger3.level == logging.DEBUG
            logger3.debug("Debug in scope")
            logger3.info("Info in scope")

        # Check level restored
        assert logger3.level == original_level
        print("   - Level restored after scope")

        # Check logs were captured
        logs3 = query_logs(db_path, test_id='test_run_3')
        assert len(logs3) == 2
        print(f"   - Captured {len(logs3)} messages in scope")
        print("   ✓ debug_scope context manager works")

        # Test 4: Query filtering
        print("\n4. Testing query filtering...")
        # Query by level
        debug_logs = query_logs(db_path, level='DEBUG')
        info_logs = query_logs(db_path, level='INFO')

        print(f"   - Found {len(debug_logs)} DEBUG logs")
        print(f"   - Found {len(info_logs)} INFO logs")

        # Query by logger
        basic_logs = query_logs(db_path, logger='test.basic')
        print(f"   - Found {len(basic_logs)} logs from 'test.basic' logger")

        assert len(basic_logs) == 3
        print("   ✓ Query filtering works")

        print("\n" + "=" * 60)
        print("✅ All tests passed!")
        print("=" * 60)

        return True

    except Exception as e:
        print(f"\n❌ Test failed: {e}")
        import traceback
        traceback.print_exc()
        return False

    finally:
        # Cleanup
        if os.path.exists(db_path):
            os.unlink(db_path)


if __name__ == '__main__':
    success = test_basic_functionality()
    sys.exit(0 if success else 1)