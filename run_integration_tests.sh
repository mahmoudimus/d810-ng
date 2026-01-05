#!/bin/bash
# Run d810-ng integration tests with IDA Pro in headless mode
#
# This script runs the full integration test suite against libobfuscated.dll
# using IDA Pro's headless mode.
#
# Usage:
#   ./run_integration_tests.sh [ida-binary]
#
# Arguments:
#   ida-binary  Path to IDA Pro binary (idat64/idat)
#               Default: idat64 (assumes it's in PATH)
#
# Environment variables:
#   IDA_PATH    Path to IDA Pro installation directory
#   COVERAGE    Set to "1" to enable coverage collection (default: 1)

set -e  # Exit on error

# Configuration
IDA_BINARY="${1:-idat64}"
BINARY_PATH="samples/bins/libobfuscated.dll"
TEST_SCRIPT="tests/run_ida_integration_tests.py"
LOG_FILE="/tmp/d810_integration_tests.log"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo "======================================================================"
echo "D810-NG Integration Test Runner"
echo "======================================================================"
echo "IDA Binary:    ${IDA_BINARY}"
echo "Test Binary:   ${BINARY_PATH}"
echo "Test Script:   ${TEST_SCRIPT}"
echo "Log File:      ${LOG_FILE}"
echo "======================================================================"

# Check if IDA is available
if ! command -v "${IDA_BINARY}" &> /dev/null; then
    echo -e "${RED}ERROR: ${IDA_BINARY} not found in PATH${NC}"
    echo ""
    echo "Please either:"
    echo "  1. Add IDA Pro to your PATH"
    echo "  2. Set IDA_PATH environment variable"
    echo "  3. Specify IDA binary as first argument"
    echo ""
    echo "Example:"
    echo "  export IDA_PATH=/path/to/ida-pro"
    echo "  ./run_integration_tests.sh \$IDA_PATH/idat64"
    exit 1
fi

# Check if binary exists
if [ ! -f "${BINARY_PATH}" ]; then
    echo -e "${RED}ERROR: Test binary not found: ${BINARY_PATH}${NC}"
    exit 1
fi

# Check if test script exists
if [ ! -f "${TEST_SCRIPT}" ]; then
    echo -e "${RED}ERROR: Test script not found: ${TEST_SCRIPT}${NC}"
    exit 1
fi

# Clean up old IDB files to force fresh analysis
IDB_FILES="${BINARY_PATH%.dll}.i64 ${BINARY_PATH%.dll}.id0 ${BINARY_PATH%.dll}.id1 ${BINARY_PATH%.dll}.nam ${BINARY_PATH%.dll}.til"
for idb_file in $IDB_FILES; do
    if [ -f "${idb_file}" ]; then
        echo "Removing old IDB file: ${idb_file}"
        rm -f "${idb_file}"
    fi
done

echo ""
echo "Running integration tests..."
echo ""

# Run IDA in headless mode with the test script
# -A: Run auto-analysis
# -S: Run script
# -L: Log file
"${IDA_BINARY}" -A -S"${TEST_SCRIPT}" -L"${LOG_FILE}" "${BINARY_PATH}"

# Capture exit code
EXIT_CODE=$?

echo ""
echo "======================================================================"

if [ ${EXIT_CODE} -eq 0 ]; then
    echo -e "${GREEN}✓ All integration tests PASSED${NC}"
    echo "======================================================================"

    # Show coverage report if available
    if command -v coverage &> /dev/null && [ -f ".coverage.integration" ]; then
        echo ""
        echo "Coverage Report:"
        echo "----------------------------------------------------------------------"
        coverage report --data-file=.coverage.integration
        echo "========================================================================"
    fi

    exit 0
else
    echo -e "${RED}✗ Integration tests FAILED (exit code: ${EXIT_CODE})${NC}"
    echo "======================================================================"
    echo ""
    echo "Check the log file for details: ${LOG_FILE}"
    echo ""

    # Show last 50 lines of log
    if [ -f "${LOG_FILE}" ]; then
        echo "Last 50 lines of log:"
        echo "----------------------------------------------------------------------"
        tail -n 50 "${LOG_FILE}"
        echo "======================================================================"
    fi

    exit ${EXIT_CODE}
fi
