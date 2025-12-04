#!/bin/bash

# Test structured logging implementation

echo "========================================"
echo "Testing Structured Logging Implementation"
echo "========================================"

# Export PYTHONPATH as per project conventions
export PYTHONPATH="${PWD}/src:${PYTHONPATH}"

# Run the simple verification first
echo ""
echo "Step 1: Running simple verification..."
echo "---------------------------------------"
python3 test_sqlite_simple.py

if [ $? -ne 0 ]; then
    echo "Simple verification failed!"
    exit 1
fi

# Run the full verification
echo ""
echo "Step 2: Running full verification..."
echo "------------------------------------"
python3 verify_structured_logging.py

if [ $? -ne 0 ]; then
    echo "Full verification failed!"
    exit 1
fi

# Run pytest tests
echo ""
echo "Step 3: Running pytest unit tests..."
echo "-------------------------------------"
python3 -m pytest tests/unit/core/test_structured_logging.py -v --tb=short

if [ $? -eq 0 ]; then
    echo ""
    echo "========================================"
    echo "✅ All tests passed successfully!"
    echo "========================================"
    exit 0
else
    echo ""
    echo "❌ Some tests failed"
    exit 1
fi