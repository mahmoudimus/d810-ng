#!/bin/bash

cd /Users/mahmoud/src/idapro/d810-ng

echo "=========================================="
echo "COMMAND 1: Check idapro module"
echo "=========================================="
python3 -c "import idapro; print('SUCCESS: idapro module available')" 2>&1 || echo "FAILED: idapro not available"

echo ""
echo "=========================================="
echo "COMMAND 2: Run pytest on structured logging test"
echo "=========================================="
PYTHONPATH=src python3 -m pytest tests/unit/core/test_structured_logging.py -v 2>&1 | head -100

echo ""
echo "=========================================="
echo "COMMAND 3: Check pytest availability"
echo "=========================================="
python3 -m pytest --version 2>&1

echo ""
echo "=========================================="
echo "COMMAND 4: List test functions"
echo "=========================================="
PYTHONPATH=src python3 -m pytest tests/unit/core/test_structured_logging.py --collect-only 2>&1 | head -50
