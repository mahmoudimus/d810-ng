#!/bin/bash
cd /Users/mahmoud/src/idapro/d810-ng
export PYTHONPATH=src:$PYTHONPATH

echo "=== Step 1: Checking idapro module ==="
python3 -c "import idapro; print('✓ idapro available')" 2>&1 || echo "✗ idapro NOT available"

echo ""
echo "=== Step 2: Checking ida64 binary ==="
which ida64 2>/dev/null && echo "✓ ida64 in PATH" || echo "✗ ida64 not in PATH"

echo ""
echo "=== Step 3: Running test_abc_patterns ==="
python3 -m pytest tests/system/test_libdeobfuscated_dsl.py::TestABCPatterns::test_abc_patterns -v -s 2>&1 | tail -100
