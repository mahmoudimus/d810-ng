#!/usr/bin/env python3
"""Lint for unsafe isinstance() calls that break on hot reload.

After hot reload, isinstance(obj, ConcreteClass) fails because class identity
changes between module load cycles. Use @runtime_checkable Protocol instead.

Usage:
    python scripts/lint_isinstance.py src/
    python scripts/lint_isinstance.py src/d810/mba/backends/ida.py

Exit codes:
    0 - No issues found (or only allowlisted)
    1 - Found unsafe isinstance() calls
"""

import ast
import sys
from pathlib import Path
from typing import NamedTuple


class Violation(NamedTuple):
    file: str
    line: int
    col: int
    class_name: str


# Classes that are safe to use with isinstance()
ALLOWLIST = {
    # Builtins
    "int", "str", "float", "bool", "bytes", "bytearray",
    "list", "dict", "tuple", "set", "frozenset",
    "type", "object", "NoneType",
    # Exceptions
    "Exception", "BaseException", "TypeError", "ValueError",
    "KeyError", "IndexError", "AttributeError", "RuntimeError",
    "StopIteration", "GeneratorExit", "AssertionError",
    # Abstract bases
    "ABC", "ABCMeta",
    # Typing
    "Protocol",  # Though Protocol itself shouldn't be used this way
    # Enum (stable identity)
    "Enum", "IntEnum", "StrEnum", "Flag", "IntFlag",
}

# Suffix patterns that indicate a Protocol (safe)
SAFE_SUFFIXES = ("Protocol", "ABC", "Base", "Interface", "Mixin")


class IsinstanceChecker(ast.NodeVisitor):
    """AST visitor to find unsafe isinstance() calls."""

    def __init__(self, filename: str):
        self.filename = filename
        self.violations: list[Violation] = []

    def visit_Call(self, node: ast.Call) -> None:
        # Check if this is isinstance(obj, class)
        if (isinstance(node.func, ast.Name)
                and node.func.id == "isinstance"
                and len(node.args) >= 2):

            class_arg = node.args[1]
            class_names = self._extract_class_names(class_arg)

            for name in class_names:
                if not self._is_safe(name):
                    self.violations.append(Violation(
                        file=self.filename,
                        line=node.lineno,
                        col=node.col_offset,
                        class_name=name,
                    ))

        self.generic_visit(node)

    def _extract_class_names(self, node: ast.expr) -> list[str]:
        """Extract class name(s) from isinstance's second argument."""
        if isinstance(node, ast.Name):
            return [node.id]
        elif isinstance(node, ast.Attribute):
            # e.g., typing.Protocol -> "Protocol"
            return [node.attr]
        elif isinstance(node, ast.Tuple):
            # isinstance(x, (A, B, C))
            names = []
            for elt in node.elts:
                names.extend(self._extract_class_names(elt))
            return names
        return []

    def _is_safe(self, name: str) -> bool:
        """Check if a class name is safe to use with isinstance()."""
        # Explicit allowlist
        if name in ALLOWLIST:
            return True
        # Safe suffix patterns (e.g., FooProtocol, FooABC)
        if name.endswith(SAFE_SUFFIXES):
            return True
        # Lowercase names are likely builtins or local vars
        if name[0].islower():
            return True
        return False


def check_file(filepath: Path) -> list[Violation]:
    """Check a single Python file for unsafe isinstance() calls."""
    try:
        source = filepath.read_text()
        tree = ast.parse(source, filename=str(filepath))
    except SyntaxError:
        return []

    checker = IsinstanceChecker(str(filepath))
    checker.visit(tree)
    return checker.violations


def main(paths: list[str]) -> int:
    """Main entry point."""
    all_violations: list[Violation] = []

    for path_str in paths:
        path = Path(path_str)
        if path.is_file() and path.suffix == ".py":
            all_violations.extend(check_file(path))
        elif path.is_dir():
            for py_file in path.rglob("*.py"):
                path_str = str(py_file)
                # Skip test files - they often need concrete isinstance
                if "/tests/" in path_str:
                    continue
                # Skip vendored third-party code
                if "/_vendor/" in path_str:
                    continue
                all_violations.extend(check_file(py_file))

    if all_violations:
        print("=" * 70)
        print("UNSAFE isinstance() CALLS (may break on hot reload)")
        print("Use @runtime_checkable Protocol for structural typing instead.")
        print("See: REFACTORING.md 'Key Lessons Learned' #8")
        print("=" * 70)
        print()

        for v in sorted(all_violations, key=lambda x: (x.file, x.line)):
            print(f"{v.file}:{v.line}:{v.col}: isinstance(_, {v.class_name})")

        print()
        print(f"Found {len(all_violations)} unsafe isinstance() calls.")
        print()
        print("To fix:")
        print("  1. Create a @runtime_checkable Protocol with required attrs/methods")
        print("  2. Replace isinstance(obj, ConcreteClass) with isinstance(obj, Protocol)")
        print()
        print("To allowlist a class, add it to ALLOWLIST in this script.")
        return 1

    print("No unsafe isinstance() calls found.")
    return 0


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print(f"Usage: {sys.argv[0]} <path> [path ...]")
        sys.exit(1)
    sys.exit(main(sys.argv[1:]))
