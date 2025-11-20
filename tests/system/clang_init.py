"""Initialize libclang for AST-based code comparison.

This module configures libclang to use the libclang.so from the IDA Pro installation.
"""
import sys
import logging
from pathlib import Path

# Ensure local clang directory is in python path
sys.path.insert(0, str(Path(__file__).parent / "clang"))

try:
    from clang.cindex import Config, Index
    CLANG_AVAILABLE = True
except ImportError as e:
    CLANG_AVAILABLE = False
    CLANG_ERROR = str(e)
    logger = logging.getLogger(__name__)
    logger.warning("clang.cindex not found: %s", e)
    Config = None
    Index = None

# Configure logging
logger = logging.getLogger(__name__)


def init_clang():
    """Initialize libclang with the library from IDA Pro installation.

    Returns:
        Index: Clang index for parsing C/C++ code

    Raises:
        RuntimeError: If clang bindings are not available
        FileNotFoundError: If libclang.so is not found
        Exception: If libclang fails to load
    """
    if not CLANG_AVAILABLE:
        raise RuntimeError(f"clang Python bindings not available: {CLANG_ERROR}")
    # Priority 1: Use libclang.so from IDA Pro installation (in Docker)
    lib_path = Path("/app/ida/libclang.so")

    # Priority 2: Use local libclang.so if available (for local development)
    if not lib_path.exists():
        lib_path = Path(__file__).parent / "libclang.so"

    if not lib_path.exists():
        raise FileNotFoundError(
            f"libclang.so not found. Expected at /app/ida/libclang.so or {lib_path}"
        )

    # Set the library file in Config
    Config.set_library_file(str(lib_path.resolve()))

    # Initialize Index (triggers the actual load)
    try:
        index = Index.create()
        logger.info("Clang loaded successfully from %s", lib_path)
        return index
    except Exception as e:
        # Common error: architecture mismatch (loading 64-bit .so in 32-bit IDA python)
        logger.error("Failed to load libclang.so: %s", e)
        raise


# Module-level index singleton
_clang_index = None


def get_clang_index():
    """Get or create the global clang index instance."""
    global _clang_index
    if _clang_index is None:
        _clang_index = init_clang()
    return _clang_index
