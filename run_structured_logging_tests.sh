#!/bin/bash

# Run structured logging tests

echo "Running structured logging unit tests..."
echo "========================================"

# Set Python path
export PYTHONPATH="${PWD}/src:${PYTHONPATH}"

# Run verification script first
echo ""
echo "1. Running verification script..."
echo "---------------------------------"
python3 verify_structured_logging.py

if [ $? -eq 0 ]; then
    echo ""
    echo "2. Running pytest unit tests..."
    echo "-------------------------------"
    # Run pytest tests
    python3 -m pytest tests/unit/core/test_structured_logging.py -v --tb=short
else
    echo "Verification script failed!"
    exit 1
fi