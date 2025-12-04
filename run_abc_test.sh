#!/bin/bash
# Run the abc_f6_or_dispatch test with all debug output

cd /Users/mahmoud/src/idapro/d810-ng

echo "=== Running abc_f6_or_dispatch test ==="
echo "Working directory: $(pwd)"
echo

# Try running with different approaches to capture output

echo "=== Attempt 1: Direct pytest run ==="
PYTHONPATH=src python -m pytest \
    tests/system/test_libdeobfuscated_dsl.py::TestABCPatterns::test_abc_patterns[abc_f6_or_dispatch] \
    -v -s --tb=short 2>&1 | head -500

echo
echo "=== Exit code: $? ==="
echo

# If that doesn't work, try running with debug logging
echo "=== Attempt 2: With debug logging ==="
PYTHONPATH=src D810_DEBUG=1 python -m pytest \
    tests/system/test_libdeobfuscated_dsl.py::TestABCPatterns::test_abc_patterns[abc_f6_or_dispatch] \
    -v -s --tb=short 2>&1 | head -500

echo
echo "=== Exit code: $? ==="