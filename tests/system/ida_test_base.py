"""Coverage-enabled test infrastructure for IDA Pro integration tests.

This module provides base test case classes that automatically handle coverage
collection during IDA Pro tests, similar to the ida-sigmaker project structure.
"""

import logging
import pathlib
import shutil
import sys
import tempfile
import unittest
import warnings

# Suppress warnings during IDA module imports
with warnings.catch_warnings():
    warnings.filterwarnings("ignore")
    import idapro
    import idaapi
    import idc
    import ida_auto
    import ida_bytes
    import ida_funcs
    import ida_hexrays
    import ida_name

# Import coverage if available
try:
    import coverage
    COVERAGE_AVAILABLE = True
except ImportError:
    COVERAGE_AVAILABLE = False
    coverage = None

logger = logging.getLogger(__name__)
logger.setLevel(logging.DEBUG)

IDA_AVAILABLE = True


class CoverageTestCase(unittest.TestCase):
    """Base test case class that automatically handles coverage collection.

    Subclasses should set the coverage_data_file class variable to specify
    where to save coverage data (e.g., '.coverage.unit', '.coverage.integration').

    Example:
        class MyTestCase(CoverageTestCase):
            coverage_data_file = '.coverage.unit'

            def test_something(self):
                # Your test code here
                pass
    """

    # Subclasses should override this to specify their coverage data file
    coverage_data_file = ".coverage"

    @classmethod
    def setUpClass(cls):
        """Set up coverage collection for the test class."""
        super().setUpClass()

        # Initialize coverage if available
        if COVERAGE_AVAILABLE:
            cls.cov = coverage.coverage(
                config_file=".coveragerc",
                check_preimported=True,
                data_file=cls.coverage_data_file,
            )
            cls.cov.start()
        else:
            cls.cov = None
            logger.warning("Coverage module not available, skipping coverage collection")

    @classmethod
    def tearDownClass(cls):
        """Stop coverage collection and save data."""
        super().tearDownClass()

        # Stop coverage and save data if it was started
        if hasattr(cls, 'cov') and cls.cov is not None:
            cls.cov.stop()
            cls.cov.save()


class CoveredIntegrationTest(CoverageTestCase):
    """Integration test base class with coverage tracking."""
    coverage_data_file = ".coverage.integration"


class IDAProTestCase(CoveredIntegrationTest):
    """Base class for IDA Pro integration tests with database management.

    This class handles:
    - Opening IDA database once for all tests
    - Running auto-analysis
    - Proper cleanup
    - Coverage collection

    Subclasses should specify the binary_name class variable.
    """

    binary_name = None  # Subclasses must override
    binary_path = None
    tempdir = None
    temp_binary_path = None
    database_opened = False

    @classmethod
    def setUpClass(cls):
        """Open IDA database once for all tests in the class."""
        if not IDA_AVAILABLE:
            raise unittest.SkipTest("IDA Pro API not available")

        if cls.binary_name is None:
            raise ValueError("Subclasses must set binary_name class variable")

        # Find the binary
        cls.tests_dir = pathlib.Path(__file__).parent
        project_root = cls.tests_dir.parent

        # Look for binary in multiple possible locations
        possible_paths = [
            project_root / "samples" / "bins" / cls.binary_name,
            project_root / "tests" / "_resources" / "bin" / cls.binary_name,
            cls.tests_dir / "bins" / cls.binary_name,
        ]

        cls.binary_path = None
        for path in possible_paths:
            if path.exists():
                cls.binary_path = path
                break

        if cls.binary_path is None:
            raise unittest.SkipTest(f"Test binary '{cls.binary_name}' not found in any expected location")

        logger.info(f"Found binary at: {cls.binary_path}")

        # Create temporary directory and copy binary for idalib compatibility
        cls.tempdir = pathlib.Path(tempfile.mkdtemp())
        cls.temp_binary_path = cls.tempdir / cls.binary_path.name
        shutil.copy(cls.binary_path, cls.temp_binary_path)

        logger.info(f"Copied binary to temp location: {cls.temp_binary_path}")

        # Open database once for all tests
        logger.info(f"Opening database {cls.temp_binary_path}...")
        result = idapro.open_database(str(cls.temp_binary_path), True)
        logger.debug(f"Open result: {result}")

        if result != 0:
            raise unittest.SkipTest(f"Failed to open database. Result code: {result}")

        # Run auto analysis
        idaapi.auto_wait()
        cls.database_opened = True

        # Store commonly used values
        cls.min_ea = idaapi.inf_get_min_ea()
        cls.max_ea = idaapi.inf_get_max_ea()

        logger.debug(f"Min EA: {hex(cls.min_ea)}, Max EA: {hex(cls.max_ea)}")

        # Debug: List all segments
        seg = idaapi.get_first_seg()
        seg_count = 0
        while seg:
            seg_count += 1
            logger.debug(
                f"Segment {seg_count}: {hex(seg.start_ea)} - {hex(seg.end_ea)}, "
                f"type: {hex(seg.type)}"
            )
            seg = idaapi.get_next_seg(seg.start_ea)

        logger.info(f"Total segments found: {seg_count}")

        # Call parent setUpClass to start coverage
        super().setUpClass()

    @classmethod
    def tearDownClass(cls):
        """Close database and clean up temporary directory."""
        if cls.database_opened:
            logger.debug("Closing database...")
            idapro.close_database()
            cls.database_opened = False

        if cls.tempdir and cls.tempdir.exists():
            logger.debug("Cleaning up temporary directory...")
            shutil.rmtree(cls.tempdir)

        # Call parent tearDownClass to stop coverage and generate reports
        super().tearDownClass()

    def get_function_ea(self, func_name):
        """Get the address of a function by name.

        Args:
            func_name: Name of the function to find

        Returns:
            Address of the function, or None if not found
        """
        ea = ida_name.get_name_ea(idaapi.BADADDR, func_name)
        if ea == idaapi.BADADDR:
            return None
        return ea

    def get_code_address(self):
        """Get a code address for testing by looking through segments.

        Returns:
            Address of code, or None if no code found
        """
        # First try to find a code segment
        seg = idaapi.get_first_seg()
        while seg:
            if seg.start_ea != idaapi.BADADDR and seg.end_ea != idaapi.BADADDR:
                # Look for code in this segment
                for ea in range(seg.start_ea, min(seg.start_ea + 0x1000, seg.end_ea)):
                    if idaapi.is_code(idaapi.get_flags(ea)):
                        logger.debug(
                            f"Found code address {hex(ea)} in segment "
                            f"{hex(seg.start_ea)}-{hex(seg.end_ea)}"
                        )
                        return ea
            seg = idaapi.get_next_seg(seg.start_ea)

        # Fallback: try linear search from min_ea
        logger.debug(f"Fallback search: min_ea={hex(self.min_ea)}, max_ea={hex(self.max_ea)}")
        for ea in range(self.min_ea, min(self.min_ea + 0x1000, self.max_ea)):
            if idaapi.is_code(idaapi.get_flags(ea)):
                logger.debug(f"Found code address {hex(ea)} in fallback search")
                return ea

        logger.warning("No code addresses found in any segments")
        return None

    def decompile_function(self, func_ea, no_cache=True):
        """Decompile a function and return the cfunc.

        Args:
            func_ea: Address of the function
            no_cache: If True, force fresh decompilation

        Returns:
            idaapi.cfuncptr_t or None if decompilation failed
        """
        if not ida_hexrays.init_hexrays_plugin():
            self.skipTest("Hex-Rays decompiler not available")

        flags = idaapi.DECOMP_NO_CACHE if no_cache else 0
        cfunc = idaapi.decompile(func_ea, flags=flags)

        return cfunc

    def get_pseudocode_string(self, cfunc):
        """Convert decompiled function to pseudocode string.

        Args:
            cfunc: Decompiled function (cfuncptr_t)

        Returns:
            String containing the pseudocode
        """
        from .stutils import pseudocode_to_string

        pseudocode = cfunc.get_pseudocode()
        return pseudocode_to_string(pseudocode)
