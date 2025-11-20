"""Test mixin for AST-based code comparison.

This mixin can be added to existing test classes to enable robust
code comparison using libclang AST parsing.
"""
import logging

logger = logging.getLogger(__name__)

try:
    from .code_comparator import CodeComparator

    CLANG_AVAILABLE = True
    CLANG_ERROR = None
except (ImportError, Exception) as e:
    CLANG_AVAILABLE = False
    CLANG_ERROR = str(e)
    logger.warning("libclang not available: %s", e)


class ASTComparisonMixin:
    """Mixin to add AST-based code comparison to test classes.

    Usage:
        class MyTest(ASTComparisonMixin, IDAProTestCase):
            def test_something(self):
                actual = decompile_function(...)
                expected = "..."
                self.assertCodeEquivalent(actual, expected)
    """

    _comparator = None

    @classmethod
    def setUpClass(cls):
        """Initialize the code comparator."""
        super().setUpClass()

        if not CLANG_AVAILABLE:
            logger.warning(
                "AST comparison not available: %s. Tests will fall back to string comparison.",
                CLANG_ERROR,
            )
            return

        try:
            cls._comparator = CodeComparator()
            logger.info("AST-based code comparison enabled")
        except Exception as e:
            logger.warning(
                "Failed to initialize CodeComparator: %s. Falling back to string comparison.",
                e,
            )

    def assertCodeEquivalent(
        self, actual: str, expected: str, msg: str = None, fallback: bool = True
    ):
        """Assert that two code snippets are structurally equivalent.

        Args:
            actual: Actual code from decompilation
            expected: Expected code
            msg: Optional message for assertion failure
            fallback: If True, fall back to assertIn checks if AST comparison unavailable

        Raises:
            AssertionError: If codes are not equivalent
        """
        if self._comparator is None:
            if not fallback:
                self.skipTest("AST comparison not available and fallback disabled")
                return

            # Fall back to basic string comparison
            # At minimum, check that key parts of expected code are in actual
            logger.debug(
                "AST comparison not available, falling back to substring checks"
            )
            # This is a simple fallback - could be improved
            if expected not in actual:
                fail_msg = f"Code mismatch.\n\nActual:\n{actual}\n\nExpected:\n{expected}"
                if msg:
                    fail_msg = f"{msg}\n\n{fail_msg}"
                self.fail(fail_msg)
            return

        # Use AST-based comparison
        try:
            self.comparator.check_equivalence(actual, expected)
        except AssertionError as e:
            if msg:
                raise AssertionError(f"{msg}\n\n{str(e)}") from e
            raise

    def assertCodeContains(
        self, actual: str, *expected_patterns: str, msg: str = None
    ):
        """Assert that code contains all expected patterns.

        This is useful for partial matching when full AST comparison is too strict.

        Args:
            actual: Actual code from decompilation
            expected_patterns: Patterns that should be in the code
            msg: Optional message for assertion failure
        """
        missing = []
        for pattern in expected_patterns:
            if pattern not in actual:
                missing.append(pattern)

        if missing:
            fail_msg = (
                f"Code missing expected patterns: {missing}\n\nActual code:\n{actual}"
            )
            if msg:
                fail_msg = f"{msg}\n\n{fail_msg}"
            self.fail(fail_msg)

    def assertCodeNotContains(self, actual: str, *forbidden_patterns: str, msg: str = None):
        """Assert that code does not contain forbidden patterns.

        This is useful for verifying that obfuscation was removed.

        Args:
            actual: Actual code from decompilation
            forbidden_patterns: Patterns that should NOT be in the code
            msg: Optional message for assertion failure
        """
        found = []
        for pattern in forbidden_patterns:
            if pattern in actual:
                found.append(pattern)

        if found:
            fail_msg = f"Code contains forbidden patterns: {found}\n\nActual code:\n{actual}"
            if msg:
                fail_msg = f"{msg}\n\n{fail_msg}"
            self.fail(fail_msg)
