#!/bin/bash
cd /Users/mahmoud/src/idapro/d810-ng

echo "=========================================="
echo "Executing pytest check script"
echo "=========================================="

python3 /Users/mahmoud/src/idapro/d810-ng/direct_test_check.py

echo ""
echo "=========================================="
echo "Attempting to run test collection"
echo "=========================================="

PYTHONPATH=src python3 -m pytest tests/system/test_libdeobfuscated_dsl.py -k abc_f6_or_dispatch --collect-only -q 2>&1 || true

echo ""
echo "=========================================="
echo "Attempting unit test"
echo "=========================================="

PYTHONPATH=src python3 -m pytest tests/unit/core/test_structured_logging.py -v --tb=short 2>&1 || true
