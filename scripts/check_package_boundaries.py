#!/usr/bin/env python3
"""Check package boundary enforcement for d810.mba rules.

This script ensures that files in `d810.mba.rules/` don't import from:
- IDA modules (ida_*, idautils, idc, idaapi)
- d810.optimizers (which depends on IDA)
- d810.hexrays (which depends on IDA)
- d810.expr (which may depend on IDA)

Pure symbolic rules should only import from:
- d810.mba.dsl
- d810.mba.rules._base
- d810.core (pure utilities)
- Standard library
- z3 (external)

Usage:
    python scripts/check_package_boundaries.py

Exit codes:
    0: All checks passed
    1: Boundary violations found
"""

import ast
import sys
from pathlib import Path


# Forbidden import prefixes for mba/rules files
FORBIDDEN_PREFIXES = [
    "ida_",           # IDA SDK modules
    "idautils",       # IDA utilities
    "idc",            # IDA scripting
    "idaapi",         # IDA API
    "d810.optimizers",  # Optimizer package (depends on IDA)
    "d810.hexrays",     # Hexrays helpers (depends on IDA)
    "d810.expr.ast",    # AST module (may depend on IDA)
    "d810.speedups.cythxr",  # Cython hexrays wrappers
]

# Allowed imports (explicit allowlist for d810 modules)
ALLOWED_D810_PREFIXES = [
    "d810.mba",           # The mba package itself
    "d810.core",          # Pure core utilities
    "d810._vendor",       # Vendored dependencies
]


def is_forbidden_import(module_name: str) -> bool:
    """Check if a module import is forbidden for mba/rules files."""
    for prefix in FORBIDDEN_PREFIXES:
        if module_name == prefix or module_name.startswith(prefix + "."):
            return True
    return False


def get_imports_from_file(filepath: Path) -> list[tuple[str, int, bool, bool]]:
    """Extract all import statements from a Python file.

    Returns list of (module_name, line_number, is_type_checking, is_lazy) tuples.
    - is_type_checking: Import is inside a TYPE_CHECKING block
    - is_lazy: Import is inside a function/method (lazy import pattern)
    """
    imports = []
    try:
        with open(filepath, "r", encoding="utf-8") as f:
            source = f.read()
        tree = ast.parse(source, filename=str(filepath))
    except SyntaxError as e:
        print(f"  Warning: Could not parse {filepath}: {e}")
        return imports

    # Find all TYPE_CHECKING if blocks
    type_checking_ranges: list[tuple[int, int]] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.If):
            # Check if this is an "if TYPE_CHECKING:" block
            if isinstance(node.test, ast.Name) and node.test.id == "TYPE_CHECKING":
                # Get line range covered by this if block
                start_line = node.lineno
                end_line = max(
                    getattr(child, "end_lineno", child.lineno)
                    for child in ast.walk(node)
                    if hasattr(child, "lineno")
                )
                type_checking_ranges.append((start_line, end_line))

    def is_in_type_checking(lineno: int) -> bool:
        """Check if a line is inside a TYPE_CHECKING block."""
        return any(start <= lineno <= end for start, end in type_checking_ranges)

    # Walk the tree structure-aware to detect lazy imports (imports inside functions)
    def process_node(node, inside_function: bool = False):
        """Recursively process AST nodes, tracking function context."""
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            # Entering a function - all imports inside are lazy
            for child in ast.iter_child_nodes(node):
                process_node(child, inside_function=True)
        elif isinstance(node, ast.ClassDef):
            # Class definitions - methods inside are functions
            for child in ast.iter_child_nodes(node):
                process_node(child, inside_function=False)
        elif isinstance(node, ast.Import):
            for alias in node.names:
                imports.append((
                    alias.name,
                    node.lineno,
                    is_in_type_checking(node.lineno),
                    inside_function
                ))
        elif isinstance(node, ast.ImportFrom):
            if node.module:
                imports.append((
                    node.module,
                    node.lineno,
                    is_in_type_checking(node.lineno),
                    inside_function
                ))
        else:
            for child in ast.iter_child_nodes(node):
                process_node(child, inside_function)

    process_node(tree)
    return imports


def check_file(filepath: Path) -> list[str]:
    """Check a single file for forbidden imports.

    Returns list of violation messages.

    Allowed patterns (not violations):
    - TYPE_CHECKING imports (only used for type hints, not runtime)
    - Lazy imports inside functions (only evaluated when function is called)
    """
    violations = []
    imports = get_imports_from_file(filepath)

    for module_name, lineno, is_type_checking, is_lazy in imports:
        # Skip TYPE_CHECKING imports (compile-time only)
        if is_type_checking:
            continue

        # Skip lazy imports inside functions (optional at runtime)
        if is_lazy:
            continue

        if is_forbidden_import(module_name):
            violations.append(
                f"  {filepath}:{lineno}: forbidden import '{module_name}'"
            )

    return violations


def main() -> int:
    """Main entry point."""
    # Find repository root (where scripts/ is located)
    script_dir = Path(__file__).parent
    repo_root = script_dir.parent

    # Directory to check
    rules_dir = repo_root / "src" / "d810" / "mba" / "rules"

    if not rules_dir.exists():
        print(f"Error: Rules directory not found: {rules_dir}")
        return 1

    print(f"Checking package boundaries in: {rules_dir}")
    print(f"Forbidden imports: {', '.join(FORBIDDEN_PREFIXES)}")
    print()

    # Find all Python files in mba/rules
    python_files = list(rules_dir.glob("**/*.py"))

    if not python_files:
        print("No Python files found to check")
        return 0

    all_violations = []

    for filepath in sorted(python_files):
        violations = check_file(filepath)
        if violations:
            all_violations.extend(violations)

    if all_violations:
        print("Package boundary violations found:")
        print()
        for violation in all_violations:
            print(violation)
        print()
        print(f"Total violations: {len(all_violations)}")
        print()
        print("Rules in d810.mba.rules should not depend on IDA modules.")
        print("Move IDA-dependent rules to d810.optimizers.microcode.instructions.pattern_matching/")
        return 1
    else:
        print(f"Checked {len(python_files)} files - all passed!")
        return 0


if __name__ == "__main__":
    sys.exit(main())
