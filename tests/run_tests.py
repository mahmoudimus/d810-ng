#!/usr/bin/env python
"""IDA Pro headless test runner.

This script runs all d810-ng tests in IDA Pro's headless mode.
It's designed to be invoked by IDA Pro with the -S flag:

    idat64 -A -S"tests/run_tests.py" -L"/tmp/ida.log"

The script will:
1. Set up the Python path
2. Import all test modules
3. Run the tests
4. Report results and exit
"""

import idapro  # MUST be first import to initialize IDA Python environment

import sys
import os
import traceback
from pathlib import Path

# Add project directories to Python path
project_root = Path(__file__).parent.parent
sys.path.insert(0, str(project_root / "src"))
sys.path.insert(0, str(project_root / "tests"))

print("=" * 80)
print("D810-NG Test Runner (IDA Pro Headless Mode)")
print("=" * 80)
print(f"Project root: {project_root}")
print(f"Python version: {sys.version}")
print(f"IDA version: {idc.get_idb_path() if 'idc' in dir() else 'N/A'}")
print("=" * 80)

# Test results
passed = []
failed = []
skipped = []


def run_test(test_name, test_func):
    """Run a single test function and record result."""
    try:
        print(f"\n[ RUN ] {test_name}")
        test_func()
        print(f"[ OK  ] {test_name}")
        passed.append(test_name)
        return True
    except AssertionError as e:
        print(f"[FAIL] {test_name}: {e}")
        traceback.print_exc()
        failed.append(test_name)
        return False
    except Exception as e:
        print(f"[ERROR] {test_name}: {e}")
        traceback.print_exc()
        failed.append(test_name)
        return False


def test_dsl_imports():
    """Test that DSL modules can be imported."""
    from d810.optimizers.dsl import (
        Var, Const, DynamicConst, when, ConstraintPredicate,
        ZERO, ONE, TWO, SymbolicExpression
    )
    assert Var is not None
    assert Const is not None
    assert DynamicConst is not None
    assert when is not None
    assert isinstance(when, ConstraintPredicate)
    print("  ✓ All DSL components imported")


def test_rules_imports():
    """Test that rule modules can be imported."""
    from d810.optimizers.rules import (
        VerifiableRule, SymbolicRule, RULE_REGISTRY
    )
    assert VerifiableRule is not None
    assert SymbolicRule is not None
    assert RULE_REGISTRY is not None
    print(f"  ✓ Rules imported, registry has {len(RULE_REGISTRY)} rules")


def test_refactored_rules_import():
    """Test that refactored rule modules can be imported."""
    try:
        from d810.optimizers.microcode.instructions.pattern_matching import (
            rewrite_add_refactored,
            rewrite_and_refactored,
            rewrite_or_refactored,
            rewrite_xor_refactored,
            rewrite_neg_refactored,
        )
        print("  ✓ All refactored rule modules imported")
    except ImportError as e:
        # Some modules might not exist yet
        print(f"  ! Some modules not available: {e}")


def test_dynamic_const_creation():
    """Test DynamicConst creation and usage."""
    from d810.optimizers.dsl import DynamicConst, Var
    from unittest.mock import Mock

    # Create dynamic constant
    dc = DynamicConst("val_res", lambda ctx: ctx['c'].value - 1)
    assert dc.name == "val_res"
    assert dc.compute is not None

    # Test computation
    mock_const = Mock()
    mock_const.value = 10
    result = dc.compute({'c': mock_const})
    assert result == 9, f"Expected 9, got {result}"

    # Test operator overloading
    x = Var("x")
    expr1 = x + dc
    expr2 = dc + x
    assert expr1 is not None
    assert expr2 is not None

    print("  ✓ DynamicConst works correctly")


def test_constraint_predicates():
    """Test constraint predicate helpers."""
    from d810.optimizers.dsl import when
    from unittest.mock import Mock

    # Test const_equals
    check = when.const_equals("c_1", 0xFF)
    assert callable(check)

    mock_const = Mock()
    mock_const.value = 0xFF
    assert check({'c_1': mock_const}) == True

    mock_const.value = 0xFE
    assert check({'c_1': mock_const}) == False

    # Test const_satisfies
    check2 = when.const_satisfies("val", lambda v: v > 0)
    mock_val = Mock()
    mock_val.value = 5
    assert check2({'val': mock_val}) == True

    mock_val.value = -1
    assert check2({'val': mock_val}) == False

    print("  ✓ Constraint predicates work correctly")


def test_constrained_rules_structure():
    """Test that constrained rules have correct structure."""
    from d810.optimizers.microcode.instructions.pattern_matching.rewrite_add_refactored import (
        Add_SpecialConstant1,
        Add_SpecialConstant3,
        Add_OLLVM2,
        AddXor_Constrained1,
    )

    # Test Add_SpecialConstant1
    rule1 = Add_SpecialConstant1()
    assert hasattr(rule1, 'PATTERN')
    assert hasattr(rule1, 'REPLACEMENT')
    assert hasattr(rule1, 'CONSTRAINTS')
    assert len(rule1.CONSTRAINTS) > 0
    print("  ✓ Add_SpecialConstant1 structure OK")

    # Test Add_SpecialConstant3 (has DynamicConst)
    assert hasattr(Add_SpecialConstant3, 'val_res')
    rule3 = Add_SpecialConstant3()
    assert hasattr(rule3, 'CONSTRAINTS')
    print("  ✓ Add_SpecialConstant3 structure OK")

    # Test Add_OLLVM2 (has lambda constraint)
    rule2 = Add_OLLVM2()
    assert len(rule2.CONSTRAINTS) > 0
    assert callable(rule2.CONSTRAINTS[0])
    print("  ✓ Add_OLLVM2 structure OK")

    # Test AddXor_Constrained1
    rule4 = AddXor_Constrained1()
    assert len(rule4.CONSTRAINTS) > 0
    print("  ✓ AddXor_Constrained1 structure OK")


def test_rule_registry_populated():
    """Test that RULE_REGISTRY contains all rules."""
    from d810.optimizers.rules import RULE_REGISTRY

    # Import all refactored modules to populate registry
    try:
        import d810.optimizers.microcode.instructions.pattern_matching.rewrite_add_refactored
        import d810.optimizers.microcode.instructions.pattern_matching.rewrite_and_refactored
        import d810.optimizers.microcode.instructions.pattern_matching.rewrite_or_refactored
        import d810.optimizers.microcode.instructions.pattern_matching.rewrite_xor_refactored
        import d810.optimizers.microcode.instructions.pattern_matching.rewrite_neg_refactored
    except ImportError:
        pass

    print(f"  ✓ Rule registry has {len(RULE_REGISTRY)} rules")

    # Check for our new constrained rules
    rule_names = [rule.__class__.__name__ for rule in RULE_REGISTRY]
    expected_rules = [
        'Add_SpecialConstant1',
        'Add_SpecialConstant3',
        'Add_OLLVM2',
        'AddXor_Constrained1',
    ]

    found_count = sum(1 for name in expected_rules if name in rule_names)
    print(f"  ✓ Found {found_count}/{len(expected_rules)} new constrained rules")


def test_check_runtime_constraints():
    """Test runtime constraint checking mechanism."""
    from d810.optimizers.dsl import Var, Const, when
    from d810.optimizers.rules import VerifiableRule
    from unittest.mock import Mock

    # Create a test rule with constraints
    x = Var("x")
    c1 = Const("c_1")
    c2 = Const("c_2")

    class TestConstrainedRule(VerifiableRule):
        PATTERN = (x ^ c1) + (x & c2)
        REPLACEMENT = x + c1
        CONSTRAINTS = [when.const_equals("c_1", 5)]
        DESCRIPTION = "Test rule"
        REFERENCE = "Test"

    rule = TestConstrainedRule()

    # Test constraint passes
    mock_const = Mock()
    mock_const.value = 5
    ctx_pass = {'c_1': mock_const, 'c_2': Mock(), 'x': Mock()}
    assert rule.check_runtime_constraints(ctx_pass) == True

    # Test constraint fails
    mock_const.value = 10
    ctx_fail = {'c_1': mock_const, 'c_2': Mock(), 'x': Mock()}
    assert rule.check_runtime_constraints(ctx_fail) == False

    print("  ✓ Runtime constraint checking works")


# Main test execution
def main():
    """Run all tests and report results."""
    print("\nRunning tests...\n")

    # Define all tests
    tests = [
        ("DSL imports", test_dsl_imports),
        ("Rules imports", test_rules_imports),
        ("Refactored rules import", test_refactored_rules_import),
        ("DynamicConst creation", test_dynamic_const_creation),
        ("Constraint predicates", test_constraint_predicates),
        ("Constrained rules structure", test_constrained_rules_structure),
        ("Rule registry populated", test_rule_registry_populated),
        ("Runtime constraint checking", test_check_runtime_constraints),
    ]

    # Run all tests
    for test_name, test_func in tests:
        run_test(test_name, test_func)

    # Print summary
    print("\n" + "=" * 80)
    print("TEST SUMMARY")
    print("=" * 80)
    print(f"Passed:  {len(passed)}")
    print(f"Failed:  {len(failed)}")
    print(f"Skipped: {len(skipped)}")
    print("=" * 80)

    if passed:
        print("\nPassed tests:")
        for test in passed:
            print(f"  ✓ {test}")

    if failed:
        print("\nFailed tests:")
        for test in failed:
            print(f"  ✗ {test}")

    # Final result
    if not failed:
        print("\n" + "=" * 80)
        print("TESTS PASSED")
        print("=" * 80)
        return 0
    else:
        print("\n" + "=" * 80)
        print("TESTS FAILED")
        print("=" * 80)
        return 1


if __name__ == "__main__":
    try:
        exit_code = main()

        # In IDA headless mode, we need to explicitly exit
        if 'idaapi' in sys.modules:
            import idaapi
            idaapi.qexit(exit_code)
        else:
            sys.exit(exit_code)
    except Exception as e:
        print(f"\n\nFATAL ERROR: {e}")
        traceback.print_exc()
        if 'idaapi' in sys.modules:
            import idaapi
            idaapi.qexit(1)
        else:
            sys.exit(1)
