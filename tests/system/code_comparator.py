"""AST-based C/C++ code comparison using libclang.

This module provides robust code comparison that ignores formatting differences
and focuses on structural/semantic equivalence.
"""
import sys
import logging
from typing import Optional
from pathlib import Path

# Ensure clang bindings are available
sys.path.insert(0, str(Path(__file__).parent / "clang"))

try:
    from clang.cindex import (
        Config,
        Index,
        TranslationUnit,
        Cursor,
        CursorKind,
        conf,
    )
    CLANG_AVAILABLE = True
except ImportError as e:
    logging.warning(
        "clang.cindex not found. AST comparison will not be available: %s", e
    )
    CLANG_AVAILABLE = False
    # Define dummy classes to prevent import errors
    Config = None
    Index = None
    TranslationUnit = None
    Cursor = None
    CursorKind = None
    conf = None

# Only import clang_init if clang is available
if CLANG_AVAILABLE:
    try:
        from .clang_init import get_clang_index
    except Exception:
        CLANG_AVAILABLE = False
        get_clang_index = None
else:
    get_clang_index = None

# Configure logging
logger = logging.getLogger(__name__)


class CodeComparator:
    """Parses and compares C/C++ code snippets for structural equivalence using Clang ASTs."""

    def __init__(self):
        """Initialize the code comparator with a clang index.

        Raises:
            RuntimeError: If libclang is not available
        """
        if not CLANG_AVAILABLE:
            raise RuntimeError(
                "libclang not available. AST comparison requires libclang Python bindings. "
                "Install with: pip install libclang"
            )
        self.index = get_clang_index()

    def _parse(self, code: str, filename: str = "dummy.cpp") -> TranslationUnit:
        """Parse a string of C/C++ code into a TranslationUnit.

        Args:
            code: C/C++ source code as string
            filename: Virtual filename for the code

        Returns:
            TranslationUnit: Parsed AST
        """
        # Compiler arguments to handle MSVC extensions (common in IDA output)
        args = [
            "-target",
            "x86_64-pc-windows-msvc",
            "-fms-extensions",
            "-fms-compatibility",
            "-w",  # Suppress warnings
            "-std=c++14",  # C++14 standard
        ]

        # Parse the code
        tu = self.index.parse(
            path=filename, args=args, unsaved_files=[(filename, code)], options=0
        )

        if tu.diagnostics:
            for diag in tu.diagnostics:
                # Log warnings/errors but proceed if possible
                # Simplified snippets might define incomplete types
                logger.debug("Clang Parse Diagnostic: %s", diag)

        return tu

    def _get_function_cursor(self, tu: TranslationUnit) -> Optional[Cursor]:
        """Find the first function declaration in the AST.

        Args:
            tu: Translation unit to search

        Returns:
            Cursor for the function, or None if not found
        """
        for cursor in tu.cursor.get_children():
            if cursor.kind == CursorKind.FUNCTION_DECL:
                return cursor
        return None

    def _normalize_spelling(self, spelling: str) -> str:
        """Normalize identifier spelling for comparison.

        This allows for minor variations while preserving semantic meaning.

        Args:
            spelling: Original identifier spelling

        Returns:
            Normalized spelling
        """
        # Strip whitespace
        return spelling.strip()

    def _cursors_equal(
        self, c1: Cursor, c2: Cursor, ignore_comments: bool = True
    ) -> bool:
        """Recursively compare two AST cursors for structural equivalence.

        Args:
            c1: First cursor
            c2: Second cursor
            ignore_comments: Whether to ignore comment nodes

        Returns:
            True if cursors are structurally equivalent
        """
        # Skip comment nodes if requested
        if ignore_comments and c1.kind in (
            CursorKind.UNEXPOSED_ATTR,
            CursorKind.DLLIMPORT_ATTR,
            CursorKind.DLLEXPORT_ATTR,
        ):
            return True

        # 1. Compare Node Kind (e.g., IF_STMT vs FOR_STMT)
        if c1.kind != c2.kind:
            logger.debug("Kind mismatch: %s vs %s", c1.kind, c2.kind)
            return False

        # 2. Compare Spelling (identifier names)
        # Allow some flexibility for compiler-generated names
        spell1 = self._normalize_spelling(c1.spelling)
        spell2 = self._normalize_spelling(c2.spelling)

        if spell1 != spell2:
            # Check if both are empty (compound statements, etc.)
            if spell1 or spell2:
                logger.debug("Spelling mismatch: '%s' vs '%s'", spell1, spell2)
                return False

        # 3. Compare Type (if applicable)
        # This catches differences like 'int' vs 'unsigned int' casts
        try:
            if c1.type.kind != c2.type.kind:
                logger.debug(
                    "Type mismatch for %s: %s vs %s",
                    c1.spelling,
                    c1.type.kind,
                    c2.type.kind,
                )
                return False
        except Exception:
            # Some cursors don't have types
            pass

        # 4. Recursively compare children
        children1 = list(c1.get_children())
        children2 = list(c2.get_children())

        # Filter out attribute nodes if ignoring comments
        if ignore_comments:
            children1 = [
                c
                for c in children1
                if c.kind
                not in (
                    CursorKind.UNEXPOSED_ATTR,
                    CursorKind.DLLIMPORT_ATTR,
                    CursorKind.DLLEXPORT_ATTR,
                )
            ]
            children2 = [
                c
                for c in children2
                if c.kind
                not in (
                    CursorKind.UNEXPOSED_ATTR,
                    CursorKind.DLLIMPORT_ATTR,
                    CursorKind.DLLEXPORT_ATTR,
                )
            ]

        if len(children1) != len(children2):
            logger.debug(
                "Child count mismatch for %s: %d vs %d",
                c1.kind,
                len(children1),
                len(children2),
            )
            return False

        for child1, child2 in zip(children1, children2):
            if not self._cursors_equal(child1, child2, ignore_comments):
                return False

        return True

    def check_equivalence(
        self, actual_code: str, expected_code: str, ignore_comments: bool = True
    ) -> None:
        """Assert that two code snippets are structurally equivalent.

        Args:
            actual_code: Code produced by deobfuscation
            expected_code: Expected code
            ignore_comments: Whether to ignore comments in comparison

        Raises:
            AssertionError: If codes are not equivalent
        """
        tu_actual = self._parse(actual_code, "actual.cpp")
        tu_expected = self._parse(expected_code, "expected.cpp")

        cursor_actual = self._get_function_cursor(tu_actual)
        cursor_expected = self._get_function_cursor(tu_expected)

        if not cursor_actual or not cursor_expected:
            raise AssertionError(
                "Could not find function definition in one or both inputs."
            )

        if not self._cursors_equal(cursor_actual, cursor_expected, ignore_comments):
            # Provide detailed error message
            raise AssertionError(
                f"Code semantic mismatch!\n\nActual:\n{actual_code}\n\nExpected:\n{expected_code}"
            )

    def are_equivalent(
        self, actual_code: str, expected_code: str, ignore_comments: bool = True
    ) -> bool:
        """Check if two code snippets are structurally equivalent.

        Args:
            actual_code: Code produced by deobfuscation
            expected_code: Expected code
            ignore_comments: Whether to ignore comments in comparison

        Returns:
            True if codes are equivalent, False otherwise
        """
        try:
            self.check_equivalence(actual_code, expected_code, ignore_comments)
            return True
        except AssertionError:
            return False
