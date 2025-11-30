"""Demonstration of AST-based code comparison for d810 tests.

This module shows how to use libclang for robust code comparison
that ignores formatting differences.
"""
import unittest
import textwrap

try:
    from .code_comparator import CodeComparator

    CLANG_AVAILABLE = True
except (ImportError, Exception) as e:
    CLANG_AVAILABLE = False
    CLANG_ERROR = str(e)


class TestASTComparison(unittest.TestCase):
    """Test the AST-based code comparison functionality."""

    @classmethod
    def setUpClass(cls):
        """Initialize the code comparator."""
        if not CLANG_AVAILABLE:
            raise unittest.SkipTest(f"libclang not available: {CLANG_ERROR}")

        try:
            cls.comparator = CodeComparator()
        except Exception as e:
            raise unittest.SkipTest(f"Failed to initialize CodeComparator: {e}")

    def assertCodeEquivalent(self, actual: str, expected: str):
        """Assert that two code snippets are structurally equivalent."""
        self.comparator.check_equivalence(actual, expected)

    def test_identical_code(self):
        """Test that identical code is recognized as equivalent."""
        code = textwrap.dedent(
            """\
            __int64 __fastcall test_func(int a1, int a2)
            {
                return a1 + a2;
            }"""
        )
        self.assertCodeEquivalent(code, code)

    def test_whitespace_differences(self):
        """Test that whitespace differences are ignored."""
        code1 = textwrap.dedent(
            """\
            __int64 __fastcall test_func(int a1, int a2)
            {
                return a1 + a2;
            }"""
        )

        code2 = textwrap.dedent(
            """\
            __int64 __fastcall test_func(int a1, int a2)
            {
                    return a1 + a2;
            }"""
        )

        self.assertCodeEquivalent(code1, code2)

    def test_comment_differences(self):
        """Test that comments are ignored."""
        code1 = textwrap.dedent(
            """\
            __int64 __fastcall test_func(int a1, int a2)
            {
                return a1 + a2;
            }"""
        )

        code2 = textwrap.dedent(
            """\
            __int64 __fastcall test_func(int a1, int a2)
            {
                // [COLLAPSED LOCAL DECLARATIONS. PRESS NUMPAD "+" TO EXPAND]

                return a1 + a2;
            }"""
        )

        self.assertCodeEquivalent(code1, code2)

    def test_semantic_difference_detected(self):
        """Test that semantic differences are detected."""
        code1 = "void func() { int a = 1 + 2; }"
        code2 = "void func() { int a = 1 - 2; }"  # Different operator

        with self.assertRaises(AssertionError):
            self.assertCodeEquivalent(code1, code2)

    def test_xor_simplification_example(self):
        """Example: XOR pattern simplification."""
        # Before d810 optimization (obfuscated XOR)
        before = textwrap.dedent(
            """\
            __int64 __fastcall test_xor(int a1, int a2, int a3, int *a4)
            {
                *a4 = a2 + a1 - 2 * (a2 & a1);
                a4[1] = a2 - 3 + a3 * a1 - 2 * ((a2 - 3) & (a3 * a1));
                return (unsigned int)(a4[1] + *a4);
            }"""
        )

        # After d810 optimization (simplified XOR)
        after = textwrap.dedent(
            """\
            __int64 __fastcall test_xor(int a1, int a2, int a3, int *a4)
            {
                // [COLLAPSED LOCAL DECLARATIONS. PRESS NUMPAD "+" TO EXPAND]

                *a4 = a2 ^ a1;
                a4[1] = (a2 - 3) ^ (a3 * a1);
                return (unsigned int)(a4[1] + *a4);
            }"""
        )

        # These are semantically DIFFERENT - the XOR is optimized
        # So this should FAIL (demonstrating that AST comparison detects real changes)
        with self.assertRaises(AssertionError):
            self.assertCodeEquivalent(before, after)

    def test_type_cast_variations(self):
        """Test that equivalent type casts are recognized."""
        code1 = "void func() { int a = (int)5; }"
        code2 = "void func() { int a = int(5); }"

        # These should be equivalent (both are int casts)
        self.assertCodeEquivalent(code1, code2)


if __name__ == "__main__":
    unittest.main()
