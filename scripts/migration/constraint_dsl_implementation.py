#!/usr/bin/env python3
"""Working implementation: Constraint DSL without lambda parsing.

This shows how to extend SymbolicExpression to support declarative constraints
like: val_res == c2 - ONE
"""

from __future__ import annotations
from dataclasses import dataclass
from typing import Any

try:
    import z3
except ImportError:
    z3 = None  # Optional for demo


# ============================================================================
# Constraint Expression Types
# ============================================================================

@dataclass
class ConstraintExpr:
    """Base class for constraint expressions."""

    def to_z3(self, z3_vars: dict[str, Any]) -> Any:
        """Convert this constraint to a Z3 boolean expression."""
        raise NotImplementedError

    def eval_and_define(self, candidate: dict) -> tuple[str | None, int | None]:
        """Evaluate constraint with concrete values.

        Returns:
            (var_name, value) if this defines a variable, else (None, None)
        """
        raise NotImplementedError

    def check(self, candidate: dict) -> bool:
        """Check if constraint holds for concrete candidate values."""
        raise NotImplementedError


@dataclass
class EqualityConstraint(ConstraintExpr):
    """Represents: left == right

    Can be either:
    1. Defining: val_res == c2 - 1 (defines val_res)
    2. Checking: c1 == ~c2 (checks relationship)
    """

    left: Any  # SymbolicExpression or AstNode
    right: Any  # SymbolicExpression or AstNode

    def to_z3(self, z3_vars: dict[str, Any]) -> Any:
        """Convert to Z3: z3_vars[left] == expr_to_z3(right, z3_vars)."""
        left_z3 = self._expr_to_z3(self.left, z3_vars)
        right_z3 = self._expr_to_z3(self.right, z3_vars)
        return left_z3 == right_z3

    def eval_and_define(self, candidate: dict) -> tuple[str | None, int | None]:
        """If left is a simple constant name, define it as right's value."""
        # Check if left is a simple constant (not an expression)
        if self._is_simple_constant(self.left):
            const_name = self._get_name(self.left)

            # Evaluate right side with candidate values
            value = self._eval_expr(self.right, candidate)
            return (const_name, value)

        return (None, None)

    def check(self, candidate: dict) -> bool:
        """Check if left == right with concrete values."""
        left_val = self._eval_expr(self.left, candidate)
        right_val = self._eval_expr(self.right, candidate)
        return left_val == right_val

    def _is_simple_constant(self, expr) -> bool:
        """Check if expression is a simple constant (not compound)."""
        # If it's SymbolicExpression wrapping AstConstant
        if hasattr(expr, 'node'):
            from d810.expr.ast import AstConstant
            return isinstance(expr.node, AstConstant)
        return False

    def _get_name(self, expr) -> str:
        """Get the name of a constant."""
        if hasattr(expr, 'node') and hasattr(expr.node, 'name'):
            return expr.node.name
        raise ValueError(f"Cannot get name from {expr}")

    def _expr_to_z3(self, expr, z3_vars: dict) -> Any:
        """Convert DSL expression to Z3."""
        from d810.expr.z3_utils import ast_to_z3_expression

        if hasattr(expr, 'node'):
            # SymbolicExpression - use the AST node
            return ast_to_z3_expression(expr.node, z3_vars)
        elif hasattr(expr, 'z3_var'):
            # Already has z3_var assigned
            return expr.z3_var
        else:
            raise ValueError(f"Cannot convert {expr} to Z3")

    def _eval_expr(self, expr, candidate: dict) -> int:
        """Evaluate expression with concrete candidate values."""
        from d810.expr.ast import AstConstant, AstLeaf, AstNode

        if hasattr(expr, 'node'):
            node = expr.node
        else:
            node = expr

        # Base cases
        if isinstance(node, AstLeaf):
            if node.name in candidate:
                return candidate[node.name].value
            raise ValueError(f"Variable {node.name} not in candidate")

        if isinstance(node, AstConstant):
            if node.name in candidate:
                return candidate[node.name].value
            if node.expected_value is not None:
                return node.expected_value
            raise ValueError(f"Constant {node.name} not in candidate and has no value")

        # Recursive case: AstNode
        if isinstance(node, AstNode):
            from ida_hexrays import m_add, m_sub, m_mul, m_and, m_or, m_xor, m_bnot, m_neg

            left_val = self._eval_expr(node.left, candidate)

            # Unary operators
            if node.right is None:
                if node.opcode == m_bnot:
                    # Bitwise NOT - need to handle width
                    width = candidate.get('_width', 32)  # Default 32-bit
                    mask = (1 << width) - 1
                    return (~left_val) & mask
                elif node.opcode == m_neg:
                    width = candidate.get('_width', 32)
                    return (-left_val) & ((1 << width) - 1)

            # Binary operators
            right_val = self._eval_expr(node.right, candidate)

            if node.opcode == m_add:
                return left_val + right_val
            elif node.opcode == m_sub:
                return left_val - right_val
            elif node.opcode == m_mul:
                return left_val * right_val
            elif node.opcode == m_and:
                return left_val & right_val
            elif node.opcode == m_or:
                return left_val | right_val
            elif node.opcode == m_xor:
                return left_val ^ right_val

            raise ValueError(f"Unknown opcode: {node.opcode}")

        raise ValueError(f"Cannot evaluate {expr}")


# ============================================================================
# Extended SymbolicExpression with constraint support
# ============================================================================

class SymbolicExpressionWithConstraints:
    """Extended SymbolicExpression that supports == for constraints.

    This is what we'd add to the existing SymbolicExpression class.
    """

    def __eq__(self, other) -> ConstraintExpr:
        """Equality constraint: self == other.

        NOTE: This overrides Python's equality operator, so:
        - x == y returns ConstraintExpr (not bool)
        - To check object equality, use `x is y`

        This is acceptable because SymbolicExpression is used for DSL,
        not as a regular Python object.
        """
        return EqualityConstraint(self, other)

    def __ne__(self, other) -> ConstraintExpr:
        """Not-equal constraint: self != other."""
        # Could implement NotEqualConstraint if needed
        raise NotImplementedError("Use ~(x == y) for not-equal")


# ============================================================================
# Integration with VerifiableRule
# ============================================================================

def enhanced_get_constraints(rule, z3_vars: dict) -> list[Any]:
    """Enhanced get_constraints() that handles ConstraintExpr objects.

    This replaces the lambda-parsing version in rules.py.
    """

    constraints = getattr(rule, 'CONSTRAINTS', [])
    z3_constraints = []

    for constraint in constraints:
        if isinstance(constraint, ConstraintExpr):
            # Direct conversion: val_res == c2 - ONE
            z3_constraints.append(constraint.to_z3(z3_vars))

        elif callable(constraint):
            # Legacy predicate: when.is_bnot(c1, c2)
            # Try auto-extraction from closure
            z3_constraint = predicate_to_z3_legacy(constraint, z3_vars)
            if z3_constraint is not None:
                z3_constraints.append(z3_constraint)

    return z3_constraints


def enhanced_check_candidate(rule, candidate: dict) -> bool:
    """Enhanced check_candidate() that handles ConstraintExpr objects.

    This would be auto-generated or used in PatternMatchingRule base class.
    """

    constraints = getattr(rule, 'CONSTRAINTS', [])

    for constraint in constraints:
        if isinstance(constraint, EqualityConstraint):
            # Try to define a new constant
            var_name, value = constraint.eval_and_define(candidate)

            if var_name is not None:
                # This is a defining constraint: val_res == c2 - 1
                # Add the computed constant to candidate
                from d810.expr.ast import AstConstant
                candidate[var_name] = AstConstant(var_name, value)
            else:
                # This is a checking constraint: c1 == ~c2
                if not constraint.check(candidate):
                    return False

        elif callable(constraint):
            # Legacy predicate
            if not constraint(candidate):
                return False

    return True


def predicate_to_z3_legacy(predicate, z3_vars: dict):
    """Legacy: extract from closure (for when.is_bnot etc)."""
    # Same as current implementation - extract from closure
    if hasattr(predicate, '__closure__') and predicate.__closure__:
        closure_vars = []
        for cell in predicate.__closure__:
            if isinstance(cell.cell_contents, str):
                closure_vars.append(cell.cell_contents)

        if len(closure_vars) >= 2:
            var1, var2 = closure_vars[0], closure_vars[1]
            if var1 in z3_vars and var2 in z3_vars:
                # Assume is_bnot
                return z3_vars[var1] == ~z3_vars[var2]

    return None


# ============================================================================
# Example Usage
# ============================================================================

if __name__ == "__main__":
    print("Constraint DSL Implementation")
    print("=" * 70)
    print()

    print("Example 1: Defining constraint")
    print("-" * 70)
    print("Code:")
    print("  val_res = Const('val_res')")
    print("  c2 = Const('c_2')")
    print("  constraint = val_res == c2 - ONE")
    print()
    print("What happens:")
    print("  1. Z3 verification: adds constraint val_res == c2 - 1")
    print("  2. Runtime matching: computes val_res = c2.value - 1")
    print()

    print("Example 2: Checking constraint")
    print("-" * 70)
    print("Code:")
    print("  c1 = Const('c_1')")
    print("  c2 = Const('c_2')")
    print("  constraint = c1 == ~c2")
    print()
    print("What happens:")
    print("  1. Z3 verification: adds constraint c1 == ~c2")
    print("  2. Runtime matching: checks if c1.value == ~c2.value")
    print()

    print("Example 3: Complete rule")
    print("-" * 70)
    print("""
class Add_SpecialConstantRule_3(VerifiableRule):
    c1, c2 = Const("c_1"), Const("c_2")
    val_res = Const("val_res")  # Symbolic

    PATTERN = (x ^ c1) + TWO * (x | c2)
    REPLACEMENT = x + val_res

    CONSTRAINTS = [
        c1 == ~c2,          # Checking constraint
        val_res == c2 - ONE  # Defining constraint
    ]
""")
    print()
    print("Benefits:")
    print("  ✓ Single source of truth")
    print("  ✓ No lambda parsing")
    print("  ✓ Same syntax for Z3 and runtime")
    print("  ✓ Composable (can add AND/OR)")
    print("  ✓ Type-checkable")
