"""System tests for D810-NG.

These tests require IDA Pro and test actual decompilation functionality.
"""

# CRITICAL: Import idapro FIRST before any IDA modules when running in headless mode!
# See: https://docs.hex-rays.com/user-guide/idalib#using-the-ida-library-python-module
# This is required for standalone test execution (idalib mode)

try:
    import idapro  # noqa: F401
except ModuleNotFoundError:
    # Not in IDA Pro environment - this is expected for unit tests
    # or when running without IDA Pro
    pass
