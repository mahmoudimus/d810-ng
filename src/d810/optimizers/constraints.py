"""Constraint expressions for declarative rule verification.

This module provides constraint expression types that allow rules to specify
constraints declaratively using operator overloading, rather than through lambda parsing.

Example:
    Instead of:
        val_res = DynamicConst("val_res", lambda ctx: ctx['c_2'].value - 1)

    Use:
        val_res = Const("val_res")
        CONSTRAINTS = [val_res == c2 - ONE]
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING, Any

if TYPE_CHECKING:
    import z3
    from d810.expr.ast import AstBase, AstConstant


@dataclass
class ConstraintExpr:
    """Base class for constraint expressions.

    Constraint expressions are created by operator overloading on SymbolicExpression.
    They serve dual purposes:
    1. Convert to Z3 constraints for verification
    2. Evaluate/check with concrete values at runtime
    """

    def to_z3(self, z3_vars: dict[str, z3.BitVecRef]) -> z3.BoolRef:
        """Convert this constraint to a Z3 boolean expression.

        Args:
            z3_vars: Mapping from variable names to Z3 BitVec variables

        Returns:
            Z3 boolean expression representing this constraint
        """
        raise NotImplementedError

    def eval_and_define(self, candidate: dict[str, Any]) -> tuple[str | None, int | None]:
        """Try to extract a variable definition from this constraint.

        If this is a defining constraint (e.g., val_res == c2 - 1), returns
        (variable_name, computed_value). Otherwise returns (None, None).

        Args:
            candidate: Dictionary mapping variable names to matched values

        Returns:
            (var_name, value) if this defines a variable, else (None, None)
        """
        raise NotImplementedError

    def check(self, candidate: dict[str, Any]) -> bool:
        """Check if this constraint holds for concrete candidate values.

        Args:
            candidate: Dictionary mapping variable names to matched values

        Returns:
            True if constraint is satisfied, False otherwise
        """
        raise NotImplementedError


@dataclass
class EqualityConstraint(ConstraintExpr):
    """Represents an equality constraint: left == right.

    Can be either:
    1. Defining constraint: val_res == c2 - 1 (defines val_res)
    2. Checking constraint: c1 == ~c2 (checks relationship)

    Attributes:
        left: Left-hand side expression
        right: Right-hand side expression
    """

    left: Any  # SymbolicExpression or AstBase
    right: Any  # SymbolicExpression or AstBase

    def to_z3(self, z3_vars: dict[str, Any]) -> Any:
        """Convert to Z3: left_z3 == right_z3."""
        left_z3 = self._expr_to_z3(self.left, z3_vars)
        right_z3 = self._expr_to_z3(self.right, z3_vars)

        import z3
        return left_z3 == right_z3

    def eval_and_define(self, candidate: dict[str, Any]) -> tuple[str | None, int | None]:
        """If left is a simple constant, define it as right's value."""
        # Check if left is a simple constant (not a compound expression)
        if self._is_simple_constant(self.left):
            const_name = self._get_name(self.left)

            # Check if this constant is already in candidate (matched from pattern)
            # If yes, this is a checking constraint, not a defining one
            if const_name in candidate:
                return (None, None)

            # Evaluate right side with candidate values
            try:
                value = self._eval_expr(self.right, candidate)
                return (const_name, value)
            except (KeyError, ValueError, AttributeError):
                # Can't evaluate yet - might be forward reference
                return (None, None)

        return (None, None)

    def check(self, candidate: dict[str, Any]) -> bool:
        """Check if left == right with concrete values."""
        try:
            left_val = self._eval_expr(self.left, candidate)
            right_val = self._eval_expr(self.right, candidate)
            return left_val == right_val
        except (KeyError, ValueError, AttributeError):
            # Can't evaluate - skip check (might be defining constraint)
            return True

    def _is_simple_constant(self, expr) -> bool:
        """Check if expression is a simple constant (not compound)."""
        from d810.expr.ast import AstConstant

        # SymbolicExpression wrapping AstConstant
        if hasattr(expr, 'node'):
            return isinstance(expr.node, AstConstant)

        # Direct AstConstant
        return isinstance(expr, AstConstant)

    def _get_name(self, expr) -> str:
        """Get the name of a constant."""
        if hasattr(expr, 'node') and hasattr(expr.node, 'name'):
            return expr.node.name
        if hasattr(expr, 'name'):
            return expr.name
        raise ValueError(f"Cannot get name from {expr}")

    def _expr_to_z3(self, expr, z3_vars: dict) -> Any:
        """Convert DSL expression to Z3.

        This converts expressions WITHOUT needing z3_var to be pre-assigned.
        It looks up variable/constant names directly in z3_vars.
        """
        import z3
        from d810.expr.ast import AstConstant, AstLeaf, AstNode
        from ida_hexrays import (
            m_add, m_sub, m_mul, m_and, m_or, m_xor,
            m_bnot, m_neg, m_shl, m_shr, m_sar
        )

        # Unwrap SymbolicExpression
        if hasattr(expr, 'node'):
            node = expr.node
        else:
            node = expr

        # Base cases: Constant or Leaf
        # IMPORTANT: Check AstConstant BEFORE AstLeaf since AstConstant inherits from AstLeaf
        if isinstance(node, AstConstant):
            # Check if it's a symbolic constant (in z3_vars)
            if node.name in z3_vars:
                return z3_vars[node.name]
            # Otherwise it's a concrete constant
            if node.expected_value is not None:
                return z3.BitVecVal(node.expected_value, 32)
            raise ValueError(f"Constant {node.name} has no value and not in z3_vars")

        if isinstance(node, AstLeaf):
            # Look up in z3_vars
            if node.name in z3_vars:
                return z3_vars[node.name]
            raise ValueError(f"Variable {node.name} not in z3_vars")

        # Recursive case: AstNode with operator
        if isinstance(node, AstNode):
            left_z3 = self._expr_to_z3(node.left, z3_vars)

            # Unary operators
            if node.right is None:
                if node.opcode == m_bnot:
                    return ~left_z3
                elif node.opcode == m_neg:
                    return -left_z3
                raise ValueError(f"Unknown unary opcode: {node.opcode}")

            # Binary operators
            right_z3 = self._expr_to_z3(node.right, z3_vars)

            if node.opcode == m_add:
                return left_z3 + right_z3
            elif node.opcode == m_sub:
                return left_z3 - right_z3
            elif node.opcode == m_mul:
                return left_z3 * right_z3
            elif node.opcode == m_and:
                return left_z3 & right_z3
            elif node.opcode == m_or:
                return left_z3 | right_z3
            elif node.opcode == m_xor:
                return left_z3 ^ right_z3
            elif node.opcode == m_shl:
                return left_z3 << right_z3
            elif node.opcode == m_shr:
                return z3.LShR(left_z3, right_z3)  # Logical shift right
            elif node.opcode == m_sar:
                return left_z3 >> right_z3  # Arithmetic shift right

            raise ValueError(f"Unknown binary opcode: {node.opcode}")

        raise ValueError(f"Cannot convert {expr} to Z3")

    def _eval_expr(self, expr, candidate: dict[str, Any]) -> int:
        """Evaluate expression with concrete candidate values.

        Args:
            expr: Expression to evaluate (SymbolicExpression or AstBase)
            candidate: Dictionary with concrete values

        Returns:
            Integer result of evaluation
        """
        from d810.expr.ast import AstConstant, AstLeaf, AstNode
        from ida_hexrays import (
            m_add, m_sub, m_mul, m_and, m_or, m_xor,
            m_bnot, m_neg, m_shl, m_shr, m_sar
        )

        # Unwrap SymbolicExpression
        if hasattr(expr, 'node'):
            node = expr.node
        else:
            node = expr

        # Base cases
        # IMPORTANT: Check AstConstant BEFORE AstLeaf since AstConstant inherits from AstLeaf
        if isinstance(node, AstConstant):
            if node.name in candidate:
                const_value = candidate[node.name]
                if hasattr(const_value, 'value'):
                    return const_value.value
                return const_value
            if node.expected_value is not None:
                return node.expected_value
            raise ValueError(f"Constant {node.name} not in candidate and has no value")

        if isinstance(node, AstLeaf):
            if node.name in candidate:
                leaf_value = candidate[node.name]
                # Handle both AstConstant/AstLeaf objects and raw integers
                if hasattr(leaf_value, 'value'):
                    return leaf_value.value
                return leaf_value
            raise ValueError(f"Variable {node.name} not in candidate")

        # Recursive case: AstNode
        if isinstance(node, AstNode):
            # Get width for masking (default 32-bit)
            width = candidate.get('_width', 32)
            mask = (1 << width) - 1

            left_val = self._eval_expr(node.left, candidate)

            # Unary operators
            if node.right is None:
                if node.opcode == m_bnot:
                    return (~left_val) & mask
                elif node.opcode == m_neg:
                    return (-left_val) & mask
                raise ValueError(f"Unknown unary opcode: {node.opcode}")

            # Binary operators
            right_val = self._eval_expr(node.right, candidate)

            if node.opcode == m_add:
                return (left_val + right_val) & mask
            elif node.opcode == m_sub:
                return (left_val - right_val) & mask
            elif node.opcode == m_mul:
                return (left_val * right_val) & mask
            elif node.opcode == m_and:
                return left_val & right_val
            elif node.opcode == m_or:
                return left_val | right_val
            elif node.opcode == m_xor:
                return left_val ^ right_val
            elif node.opcode == m_shl:
                return (left_val << right_val) & mask
            elif node.opcode == m_shr:
                return (left_val >> right_val) & mask
            elif node.opcode == m_sar:
                # Arithmetic right shift - preserve sign bit
                if left_val & (1 << (width - 1)):
                    # Negative - fill with 1s
                    return (left_val >> right_val) | (~mask >> right_val)
                return left_val >> right_val

            raise ValueError(f"Unknown binary opcode: {node.opcode}")

        raise ValueError(f"Cannot evaluate {expr}")


def is_constraint_expr(obj: Any) -> bool:
    """Check if an object is a ConstraintExpr instance."""
    return isinstance(obj, ConstraintExpr)
