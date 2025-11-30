#!/usr/bin/env python
"""Local test runner for d810-ng DSL extensions (no IDA required).

This script tests the DSL infrastructure without requiring IDA Pro.
It validates syntax, imports (mocked), and basic functionality.

Usage:
    python tests/run_tests_local.py
"""

import sys
import os
from pathlib import Path

# Add project directories to Python path
project_root = Path(__file__).parent.parent
sys.path.insert(0, str(project_root / "src"))
sys.path.insert(0, str(project_root / "tests"))

print("=" * 80)
print("D810-NG Local Test Runner (No IDA Required)")
print("=" * 80)
print(f"Project root: {project_root}")
print(f"Python version: {sys.version}")
print("=" * 80)

passed = []
failed = []


def run_test(test_name, test_func):
    """Run a single test and record result."""
    try:
        print(f"\n[ RUN ] {test_name}")
        test_func()
        print(f"[ OK  ] {test_name}")
        passed.append(test_name)
        return True
    except Exception as e:
        print(f"[FAIL] {test_name}: {e}")
        import traceback
        traceback.print_exc()
        failed.append(test_name)
        return False


def test_syntax_validation():
    """Validate Python syntax of all files."""
    import ast

    files_to_check = [
        "src/d810/optimizers/dsl.py",
        "src/d810/optimizers/rules.py",
        "src/d810/optimizers/microcode/instructions/pattern_matching/rewrite_add_refactored.py",
        "src/d810/optimizers/microcode/instructions/pattern_matching/rewrite_and_refactored.py",
        "src/d810/optimizers/microcode/instructions/pattern_matching/rewrite_or_refactored.py",
        "src/d810/optimizers/microcode/instructions/pattern_matching/rewrite_bnot_refactored.py",
        "src/d810/optimizers/microcode/instructions/pattern_matching/rewrite_predicates_refactored.py",
        "src/d810/optimizers/microcode/instructions/pattern_matching/rewrite_xor_refactored.py",
        "src/d810/optimizers/microcode/instructions/pattern_matching/rewrite_neg_refactored.py",
        "src/d810/optimizers/microcode/instructions/pattern_matching/rewrite_sub_refactored.py",
        "src/d810/optimizers/microcode/instructions/pattern_matching/rewrite_mul_refactored.py",
        "src/d810/optimizers/microcode/instructions/pattern_matching/rewrite_mov_refactored.py",
        "src/d810/optimizers/microcode/instructions/pattern_matching/rewrite_cst_refactored.py",
        "tests/unit/optimizers/test_dsl_extensions.py",
    ]

    for filepath in files_to_check:
        full_path = project_root / filepath
        if not full_path.exists():
            print(f"  ! {filepath} not found (skipping)")
            continue

        with open(full_path) as f:
            try:
                ast.parse(f.read())
                print(f"  ✓ {filepath}")
            except SyntaxError as e:
                raise AssertionError(f"Syntax error in {filepath}: {e}")


def test_file_structure():
    """Verify file structure and organization."""
    required_files = [
        "src/d810/optimizers/dsl.py",
        "src/d810/optimizers/rules.py",
        "src/d810/optimizers/core.py",
        "tests/unit/optimizers/test_dsl_extensions.py",
    ]

    for filepath in required_files:
        full_path = project_root / filepath
        assert full_path.exists(), f"Required file missing: {filepath}"
        print(f"  ✓ {filepath}")


def test_documentation_exists():
    """Verify documentation files exist."""
    docs = [
        "MIGRATION_GUIDE.md",
        "REFACTORING.md",
    ]

    for doc in docs:
        full_path = project_root / doc
        assert full_path.exists(), f"Documentation missing: {doc}"
        print(f"  ✓ {doc}")


def test_dsl_class_definitions():
    """Test that DSL classes are defined with correct structure."""
    import ast

    dsl_file = project_root / "src/d810/optimizers/dsl.py"
    with open(dsl_file) as f:
        tree = ast.parse(f.read())

    # Find class definitions
    classes = [node for node in ast.walk(tree) if isinstance(node, ast.ClassDef)]
    class_names = [cls.name for cls in classes]

    expected_classes = [
        'SymbolicExpression',
        'DynamicConst',
        'ConstraintPredicate',
    ]

    for expected in expected_classes:
        assert expected in class_names, f"Class {expected} not found"
        print(f"  ✓ {expected} class defined")

    # Check for singleton
    assigns = [node for node in ast.walk(tree) if isinstance(node, ast.Assign)]
    assign_names = []
    for assign in assigns:
        for target in assign.targets:
            if isinstance(target, ast.Name):
                assign_names.append(target.id)

    assert 'when' in assign_names, "Singleton 'when' not defined"
    print("  ✓ 'when' singleton defined")


def test_rules_class_definitions():
    """Test that rule classes are defined correctly."""
    import ast

    rules_file = project_root / "src/d810/optimizers/rules.py"
    with open(rules_file) as f:
        tree = ast.parse(f.read())

    classes = [node for node in ast.walk(tree) if isinstance(node, ast.ClassDef)]
    class_names = [cls.name for cls in classes]

    expected_classes = [
        'SymbolicRule',
        'VerifiableRule',
    ]

    for expected in expected_classes:
        assert expected in class_names, f"Class {expected} not found"
        print(f"  ✓ {expected} class defined")

    # Check for RULE_REGISTRY (handles both ast.Assign and ast.AnnAssign)
    assign_names = []

    # Regular assignments: x = value
    assigns = [node for node in ast.walk(tree) if isinstance(node, ast.Assign)]
    for assign in assigns:
        for target in assign.targets:
            if isinstance(target, ast.Name):
                assign_names.append(target.id)

    # Annotated assignments: x: Type = value
    ann_assigns = [node for node in ast.walk(tree) if isinstance(node, ast.AnnAssign)]
    for ann_assign in ann_assigns:
        if isinstance(ann_assign.target, ast.Name):
            assign_names.append(ann_assign.target.id)

    assert 'RULE_REGISTRY' in assign_names, "RULE_REGISTRY not defined"
    print("  ✓ RULE_REGISTRY defined")


def test_constrained_rules_exist():
    """Test that constrained rules are defined."""
    import ast

    add_refactored = project_root / "src/d810/optimizers/microcode/instructions/pattern_matching/rewrite_add_refactored.py"

    if not add_refactored.exists():
        print("  ! rewrite_add_refactored.py not found (skipping)")
        return

    with open(add_refactored) as f:
        tree = ast.parse(f.read())

    classes = [node for node in ast.walk(tree) if isinstance(node, ast.ClassDef)]
    class_names = [cls.name for cls in classes]

    expected_rules = [
        'Add_SpecialConstant1',
        'Add_SpecialConstant2',
        'Add_SpecialConstant3',
        'Add_OLLVM2',
        'Add_OLLVM4',
        'AddXor_Constrained1',
        'AddXor_Constrained2',
    ]

    found = 0
    for expected in expected_rules:
        if expected in class_names:
            found += 1
            print(f"  ✓ {expected} defined")

    assert found > 0, "No constrained rules found"
    print(f"  ✓ Found {found}/{len(expected_rules)} constrained rules")


def test_code_metrics():
    """Calculate and report code metrics."""
    def count_lines(filepath):
        """Count non-empty, non-comment lines."""
        with open(filepath) as f:
            lines = f.readlines()

        code_lines = 0
        for line in lines:
            stripped = line.strip()
            if stripped and not stripped.startswith('#'):
                code_lines += 1
        return code_lines

    files = {
        "dsl.py": "src/d810/optimizers/dsl.py",
        "rules.py": "src/d810/optimizers/rules.py",
        "rewrite_add_refactored.py": "src/d810/optimizers/microcode/instructions/pattern_matching/rewrite_add_refactored.py",
    }

    total_lines = 0
    for name, path in files.items():
        full_path = project_root / path
        if full_path.exists():
            lines = count_lines(full_path)
            total_lines += lines
            print(f"  {name}: {lines} lines")

    print(f"  ✓ Total: {total_lines} lines of code")


def test_workflow_exists():
    """Test that GitHub workflow is set up."""
    workflow_file = project_root / ".github/workflows/test-ida.yml"

    if workflow_file.exists():
        print(f"  ✓ GitHub workflow exists")
        with open(workflow_file) as f:
            content = f.read()
            assert 'test' in content.lower(), "Workflow missing test job"
            assert 'ida' in content.lower(), "Workflow not configured for IDA"
            print(f"  ✓ Workflow configured for IDA testing")
    else:
        print(f"  ! GitHub workflow not found (optional)")


def main():
    """Run all tests and report results."""
    print("\nRunning local tests...\n")

    tests = [
        ("Syntax validation", test_syntax_validation),
        ("File structure", test_file_structure),
        ("Documentation exists", test_documentation_exists),
        ("DSL class definitions", test_dsl_class_definitions),
        ("Rules class definitions", test_rules_class_definitions),
        ("Constrained rules exist", test_constrained_rules_exist),
        ("Code metrics", test_code_metrics),
        ("GitHub workflow", test_workflow_exists),
    ]

    for test_name, test_func in tests:
        run_test(test_name, test_func)

    # Summary
    print("\n" + "=" * 80)
    print("TEST SUMMARY")
    print("=" * 80)
    print(f"Passed:  {len(passed)}")
    print(f"Failed:  {len(failed)}")
    print("=" * 80)

    if passed:
        print("\n✓ Passed tests:")
        for test in passed:
            print(f"  • {test}")

    if failed:
        print("\n✗ Failed tests:")
        for test in failed:
            print(f"  • {test}")

    if not failed:
        print("\n" + "=" * 80)
        print("ALL TESTS PASSED ✓")
        print("=" * 80)
        print("\nNext steps:")
        print("  1. Run full tests in IDA Pro: tests/run_tests.py")
        print("  2. Run GitHub Actions workflow for CI/CD")
        print("  3. Check MIGRATION_GUIDE.md for usage examples")
        return 0
    else:
        print("\n" + "=" * 80)
        print("SOME TESTS FAILED ✗")
        print("=" * 80)
        return 1


if __name__ == "__main__":
    sys.exit(main())
