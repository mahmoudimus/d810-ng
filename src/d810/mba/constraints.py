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

    def __call__(self, candidate: dict[str, Any]) -> bool:
        """Make constraints callable for backward compatibility.

        This allows existing code that expects `constraint(match_context)` to work.

        Args:
            candidate: Dictionary mapping variable names to matched values

        Returns:
            True if constraint is satisfied, False otherwise
        """
        return self.check(candidate)

    def __and__(self, other: ConstraintExpr) -> ConstraintExpr:
        """Logical AND: self & other."""
        return AndConstraint(self, other)

    def __or__(self, other: ConstraintExpr) -> ConstraintExpr:
        """Logical OR: self | other."""
        return OrConstraint(self, other)

    def __invert__(self) -> ConstraintExpr:
        """Logical NOT: ~self."""
        return NotConstraint(self)

    def to_int(self) -> "SymbolicExpression":
        """Convert boolean constraint to integer expression (0 or 1).

        This bridges the gap between boolean constraints (formulas) and arithmetic
        expressions (terms). In C-like languages and IDA microcode, comparison
        results are treated as integers (0 for false, 1 for true).

        Equivalent to:
        - C: (int)(x != y)
        - Z3: If(x != y, 1, 0)
        - IDA: SETNZ, SETZ instructions

        Example:
            >>> x = Var("x")
            >>> constraint = x != Const("0", 0)  # Returns ConstraintExpr (boolean)
            >>> int_expr = constraint.to_int()   # Returns SymbolicExpression (0 or 1)
            >>> pattern = int_expr + Const("5", 5)  # Now can use in arithmetic!

        Returns:
            SymbolicExpression representing 0 (false) or 1 (true)
        """
        from d810.mba.dsl import SymbolicExpression
        return SymbolicExpression(operation="bool_to_int", constraint=self)


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
        from d810.mba.dsl import SymbolicExpression
        from d810.expr.ast import AstConstant

        # Pure SymbolicExpression leaf
        if isinstance(expr, SymbolicExpression):
            return expr.is_leaf() and expr.name is not None

        # SymbolicExpression wrapping AstConstant (legacy)
        if hasattr(expr, 'node'):
            return isinstance(expr.node, AstConstant)

        # Direct AstConstant (legacy)
        return isinstance(expr, AstConstant)

    def _get_name(self, expr) -> str:
        """Get the name of a constant."""
        from d810.mba.dsl import SymbolicExpression

        # Pure SymbolicExpression
        if isinstance(expr, SymbolicExpression):
            if expr.name:
                return expr.name
            raise ValueError(f"SymbolicExpression has no name: {expr}")

        # Legacy: AstNode/AstConstant
        if hasattr(expr, 'node') and hasattr(expr.node, 'name'):
            return expr.node.name
        if hasattr(expr, 'name'):
            return expr.name
        raise ValueError(f"Cannot get name from {expr}")

    def _expr_to_z3(self, expr, z3_vars: dict) -> Any:
        """Convert DSL expression to Z3.

        This converts SymbolicExpression directly to Z3 using the Z3VerificationVisitor.
        """
        import z3
        from d810.mba.dsl import SymbolicExpression

        # If it's a SymbolicExpression, use Z3VerificationVisitor
        if isinstance(expr, SymbolicExpression):
            from d810.mba.visitors import Z3VerificationVisitor
            visitor = Z3VerificationVisitor(bit_width=32, var_map=z3_vars)
            return visitor.visit(expr)

        # Legacy path: Handle old AstNode-based expressions
        from d810.expr.ast import AstConstant, AstLeaf, AstNode

        # Unwrap SymbolicExpression to node if needed
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

        # Recursive case: AstNode with operator (legacy path - use opcodes)
        if isinstance(node, AstNode):
            # Use platform-independent opcodes for comparison
            import d810.opcodes as opc

            left_z3 = self._expr_to_z3(node.left, z3_vars)

            # Unary operators
            if node.right is None:
                if node.opcode == opc.M_BNOT:
                    return ~left_z3
                elif node.opcode == opc.M_NEG:
                    return -left_z3
                raise ValueError(f"Unknown unary opcode: {node.opcode}")

            # Binary operators
            right_z3 = self._expr_to_z3(node.right, z3_vars)

            if node.opcode == opc.M_ADD:
                return left_z3 + right_z3
            elif node.opcode == opc.M_SUB:
                return left_z3 - right_z3
            elif node.opcode == opc.M_MUL:
                return left_z3 * right_z3
            elif node.opcode == opc.M_AND:
                return left_z3 & right_z3
            elif node.opcode == opc.M_OR:
                return left_z3 | right_z3
            elif node.opcode == opc.M_XOR:
                return left_z3 ^ right_z3
            elif node.opcode == opc.M_SHL:
                return left_z3 << right_z3
            elif node.opcode == opc.M_SHR:
                return z3.LShR(left_z3, right_z3)  # Logical shift right
            elif node.opcode == opc.M_SAR:
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
        from d810.mba.dsl import SymbolicExpression

        # If it's a SymbolicExpression, evaluate directly
        if isinstance(expr, SymbolicExpression):
            return self._eval_symbolic_expr(expr, candidate)

        # Legacy path: Handle AstNode-based expressions
        from d810.expr.ast import AstConstant, AstLeaf, AstNode
        import d810.opcodes as opc

        # Unwrap SymbolicExpression to node if needed
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
                if node.opcode == opc.M_BNOT:
                    return (~left_val) & mask
                elif node.opcode == opc.M_NEG:
                    return (-left_val) & mask
                raise ValueError(f"Unknown unary opcode: {node.opcode}")

            # Binary operators
            right_val = self._eval_expr(node.right, candidate)

            if node.opcode == opc.M_ADD:
                return (left_val + right_val) & mask
            elif node.opcode == opc.M_SUB:
                return (left_val - right_val) & mask
            elif node.opcode == opc.M_MUL:
                return (left_val * right_val) & mask
            elif node.opcode == opc.M_AND:
                return left_val & right_val
            elif node.opcode == opc.M_OR:
                return left_val | right_val
            elif node.opcode == opc.M_XOR:
                return left_val ^ right_val
            elif node.opcode == opc.M_SHL:
                return (left_val << right_val) & mask
            elif node.opcode == opc.M_SHR:
                return (left_val >> right_val) & mask
            elif node.opcode == opc.M_SAR:
                # Arithmetic right shift - preserve sign bit
                if left_val & (1 << (width - 1)):
                    # Negative - fill with 1s
                    return (left_val >> right_val) | (~mask >> right_val)
                return left_val >> right_val

            raise ValueError(f"Unknown binary opcode: {node.opcode}")

        raise ValueError(f"Cannot evaluate {expr}")

    def _eval_symbolic_expr(self, expr, candidate: dict[str, Any]) -> int:
        """Evaluate a pure SymbolicExpression with concrete values."""
        from d810.mba.dsl import SymbolicExpression

        # Get width for masking (default 32-bit)
        width = candidate.get('_width', 32)
        mask = (1 << width) - 1

        # Leaf node
        if expr.is_leaf():
            if expr.name in candidate:
                value = candidate[expr.name]
                if hasattr(value, 'value'):
                    return value.value
                return value
            if expr.value is not None:
                return expr.value
            raise ValueError(f"Variable/constant {expr.name} not in candidate")

        # Operation node - evaluate recursively
        left_val = self._eval_symbolic_expr(expr.left, candidate) if expr.left else None
        right_val = self._eval_symbolic_expr(expr.right, candidate) if expr.right else None

        match expr.operation:
            case "neg":
                return (-left_val) & mask
            case "bnot":
                return (~left_val) & mask
            case "add":
                return (left_val + right_val) & mask
            case "sub":
                return (left_val - right_val) & mask
            case "mul":
                return (left_val * right_val) & mask
            case "and":
                return left_val & right_val
            case "or":
                return left_val | right_val
            case "xor":
                return left_val ^ right_val
            case "shl":
                return (left_val << right_val) & mask
            case "shr":
                return (left_val >> right_val) & mask
            case "sar":
                # Arithmetic right shift - preserve sign bit
                if left_val & (1 << (width - 1)):
                    # Negative - fill with 1s
                    return (left_val >> right_val) | (~mask >> right_val)
                return left_val >> right_val
            case _:
                raise ValueError(f"Unknown operation: {expr.operation}")


@dataclass
class ComparisonConstraint(ConstraintExpr):
    """Represents a comparison constraint: left op right.

    Supports !=, <, >, <=, >= operations.

    Attributes:
        left: Left-hand side expression
        right: Right-hand side expression
        op_symbol: String representation of operator (for display)
        op_name: Operation name ("ne", "lt", "gt", "le", "ge")
    """

    left: Any  # SymbolicExpression or AstBase
    right: Any  # SymbolicExpression or AstBase
    op_symbol: str  # For display: "!=", "<", ">", "<=", ">="
    op_name: str    # Internal: "ne", "lt", "gt", "le", "ge"

    def to_z3(self, z3_vars: dict[str, Any]) -> Any:
        """Convert to Z3 comparison."""
        import z3

        # Reuse EqualityConstraint's conversion logic
        eq_constraint = EqualityConstraint(self.left, self.right)
        left_z3 = eq_constraint._expr_to_z3(self.left, z3_vars)
        right_z3 = eq_constraint._expr_to_z3(self.right, z3_vars)

        match self.op_name:
            case "ne":
                return left_z3 != right_z3
            case "lt":
                return z3.ULT(left_z3, right_z3)  # Unsigned less than
            case "gt":
                return z3.UGT(left_z3, right_z3)  # Unsigned greater than
            case "le":
                return z3.ULE(left_z3, right_z3)  # Unsigned less or equal
            case "ge":
                return z3.UGE(left_z3, right_z3)  # Unsigned greater or equal
            case _:
                raise ValueError(f"Unknown comparison: {self.op_name}")

    def eval_and_define(self, candidate: dict[str, Any]) -> tuple[str | None, int | None]:
        """Comparisons don't define variables."""
        return (None, None)

    def check(self, candidate: dict[str, Any]) -> bool:
        """Check if comparison holds with concrete values."""
        try:
            eq_constraint = EqualityConstraint(self.left, self.right)
            left_val = eq_constraint._eval_expr(self.left, candidate)
            right_val = eq_constraint._eval_expr(self.right, candidate)

            match self.op_name:
                case "ne":
                    return left_val != right_val
                case "lt":
                    return left_val < right_val
                case "gt":
                    return left_val > right_val
                case "le":
                    return left_val <= right_val
                case "ge":
                    return left_val >= right_val
                case _:
                    raise ValueError(f"Unknown comparison: {self.op_name}")
        except (KeyError, ValueError, AttributeError):
            # Can't evaluate
            return False

    def __repr__(self) -> str:
        return f"({self.left} {self.op_symbol} {self.right})"


@dataclass
class AndConstraint(ConstraintExpr):
    """Logical AND of two constraints.

    Attributes:
        left: Left constraint
        right: Right constraint
    """

    left: ConstraintExpr
    right: ConstraintExpr

    def to_z3(self, z3_vars: dict[str, Any]) -> Any:
        """Convert to Z3: And(left_z3, right_z3)."""
        import z3
        left_z3 = self.left.to_z3(z3_vars)
        right_z3 = self.right.to_z3(z3_vars)
        return z3.And(left_z3, right_z3)

    def eval_and_define(self, candidate: dict[str, Any]) -> tuple[str | None, int | None]:
        """Try to extract definitions from left first, then right."""
        # Try left constraint
        var_name, value = self.left.eval_and_define(candidate)
        if var_name is not None:
            return (var_name, value)

        # Try right constraint
        return self.right.eval_and_define(candidate)

    def check(self, candidate: dict[str, Any]) -> bool:
        """Both constraints must hold."""
        return self.left.check(candidate) and self.right.check(candidate)

    def __repr__(self) -> str:
        return f"({self.left} && {self.right})"


@dataclass
class OrConstraint(ConstraintExpr):
    """Logical OR of two constraints.

    Attributes:
        left: Left constraint
        right: Right constraint
    """

    left: ConstraintExpr
    right: ConstraintExpr

    def to_z3(self, z3_vars: dict[str, Any]) -> Any:
        """Convert to Z3: Or(left_z3, right_z3)."""
        import z3
        left_z3 = self.left.to_z3(z3_vars)
        right_z3 = self.right.to_z3(z3_vars)
        return z3.Or(left_z3, right_z3)

    def eval_and_define(self, candidate: dict[str, Any]) -> tuple[str | None, int | None]:
        """OR doesn't define variables - both branches would need same value."""
        return (None, None)

    def check(self, candidate: dict[str, Any]) -> bool:
        """At least one constraint must hold."""
        return self.left.check(candidate) or self.right.check(candidate)

    def __repr__(self) -> str:
        return f"({self.left} || {self.right})"


@dataclass
class NotConstraint(ConstraintExpr):
    """Logical NOT of a constraint.

    Attributes:
        operand: The constraint to negate
    """

    operand: ConstraintExpr

    def to_z3(self, z3_vars: dict[str, Any]) -> Any:
        """Convert to Z3: Not(operand_z3)."""
        import z3
        operand_z3 = self.operand.to_z3(z3_vars)
        return z3.Not(operand_z3)

    def eval_and_define(self, candidate: dict[str, Any]) -> tuple[str | None, int | None]:
        """NOT doesn't define variables."""
        return (None, None)

    def check(self, candidate: dict[str, Any]) -> bool:
        """Negate the operand's result."""
        return not self.operand.check(candidate)

    def __repr__(self) -> str:
        return f"!({self.operand})"


def is_constraint_expr(obj: Any) -> bool:
    """Check if an object is a ConstraintExpr instance."""
    return isinstance(obj, ConstraintExpr)
