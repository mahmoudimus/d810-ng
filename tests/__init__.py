# CRITICAL: Import idapro FIRST before any IDA modules!
# See: https://docs.hex-rays.com/user-guide/idalib#using-the-ida-library-python-module
import idapro  # noqa: F401

import pathlib
import sys

# Ensure 'd810' is importable by adding the sibling 'src' directory to sys.path
current_dir = pathlib.Path(__file__).resolve().parent
src_path = current_dir.parent / "src"
if str(src_path) not in sys.path:
    sys.path.insert(0, str(src_path))

# Import idapro BEFORE any d810 modules that use IDA APIs
# This is required for standalone test execution (idalib mode)
# Only import if available (when running in IDA Pro environment)
try:
    import idapro
except ModuleNotFoundError:
    pass  # Not in IDA Pro environment, skip idapro import
