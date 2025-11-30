#!/usr/bin/env python3
"""Test the new constraint DSL implementation.

This script tests the ConstraintExpr functionality without needing IDA.
"""

import sys
sys.path.insert(0, '/home/user/d810-ng/src')

from d810.optimizers.constraints import EqualityConstraint, is_constraint_expr
from d810.expr.ast import AstConstant, AstLeaf, AstNode
from ida_hexrays import m_add, m_sub, m_bnot


def test_equality_constraint_check():
    """Test checking constraint: c1 == ~c2."""
    print("Test 1: Checking constraint (c1 == ~c2)")
    print("-" * 60)

    c1 = AstConstant("c_1", 0xFE)  # 254
    c2 = AstConstant("c_2", 0x01)  # 1

    constraint = EqualityConstraint(c1, AstNode(m_bnot, c2))

    # Test with matching values (254 == ~1 in 8-bit)
    candidate = {"c_1": c1, "c_2": c2, "_width": 8}

    result = constraint.check(candidate)
    print(f"  c1 value: {c1.expected_value} (0x{c1.expected_value:02x})")
    print(f"  c2 value: {c2.expected_value} (0x{c2.expected_value:02x})")
    print(f"  ~c2 (8-bit): {~c2.expected_value & 0xFF} (0x{~c2.expected_value & 0xFF:02x})")
    print(f"  Constraint holds: {result}")
    assert result, "Constraint should hold for 0xFE == ~0x01"
    print("  ✓ PASSED\n")


def test_equality_constraint_define():
    """Test defining constraint: val_res == c2 - 1."""
    print("Test 2: Defining constraint (val_res == c2 - 1)")
    print("-" * 60)

    c2 = AstConstant("c_2", 5)
    val_res = AstConstant("val_res", None)  # Undefined, to be computed
    one = AstConstant("ONE", 1)

    constraint = EqualityConstraint(val_res, AstNode(m_sub, c2, one))

    # Test definition extraction
    candidate = {"c_2": c2, "ONE": one}

    var_name, value = constraint.eval_and_define(candidate)
    print(f"  c2 value: {c2.expected_value}")
    print(f"  Extracted definition: {var_name} = {value}")
    assert var_name == "val_res", "Should extract val_res"
    assert value == 4, "Should compute 5 - 1 = 4"
    print("  ✓ PASSED\n")


def test_is_constraint_expr():
    """Test is_constraint_expr() helper."""
    print("Test 3: is_constraint_expr() helper")
    print("-" * 60)

    c1 = AstConstant("c_1", 1)
    c2 = AstConstant("c_2", 2)
    constraint = EqualityConstraint(c1, c2)

    assert is_constraint_expr(constraint), "Should recognize ConstraintExpr"
    assert not is_constraint_expr(c1), "Should not recognize AstConstant"
    assert not is_constraint_expr(lambda x: True), "Should not recognize callable"
    print("  ✓ PASSED\n")


def test_symbolic_expression_eq_operator():
    """Test that SymbolicExpression.__eq__ creates ConstraintExpr."""
    print("Test 4: SymbolicExpression.__eq__ operator")
    print("-" * 60)

    from d810.optimizers.dsl import Const

    # This would fail without __eq__ override
    c1 = Const("c_1")
    c2 = Const("c_2")

    constraint = c1 == c2  # Should create EqualityConstraint

    assert is_constraint_expr(constraint), "c1 == c2 should create ConstraintExpr"
    assert isinstance(constraint, EqualityConstraint), "Should be EqualityConstraint"
    print(f"  Type of (c1 == c2): {type(constraint).__name__}")
    print("  ✓ PASSED\n")


def test_complex_expression_constraint():
    """Test constraint with complex expression: val_res == c2 - ONE."""
    print("Test 5: Complex expression constraint")
    print("-" * 60)

    from d810.optimizers.dsl import Const

    c2 = Const("c_2")
    ONE = Const("ONE", 1)
    val_res = Const("val_res")

    # Create constraint using DSL: val_res == c2 - ONE
    constraint = val_res == c2 - ONE

    assert is_constraint_expr(constraint), "Should be ConstraintExpr"

    # Test evaluation with concrete values
    from d810.expr.ast import AstConstant
    candidate = {
        "c_2": AstConstant("c_2", 10),
        "ONE": AstConstant("ONE", 1),
    }

    var_name, value = constraint.eval_and_define(candidate)
    print(f"  Constraint: val_res == c2 - ONE")
    print(f"  With c2=10, ONE=1")
    print(f"  Extracted: {var_name} = {value}")
    assert var_name == "val_res", "Should extract val_res"
    assert value == 9, "Should compute 10 - 1 = 9"
    print("  ✓ PASSED\n")


def main():
    """Run all tests."""
    print("=" * 60)
    print("Constraint DSL Tests")
    print("=" * 60)
    print()

    try:
        test_equality_constraint_check()
        test_equality_constraint_define()
        test_is_constraint_expr()
        test_symbolic_expression_eq_operator()
        test_complex_expression_constraint()

        print("=" * 60)
        print("All tests PASSED! ✓")
        print("=" * 60)
        return 0

    except Exception as e:
        print()
        print("=" * 60)
        print(f"Test FAILED: {e}")
        print("=" * 60)
        import traceback
        traceback.print_exc()
        return 1


if __name__ == "__main__":
    sys.exit(main())
