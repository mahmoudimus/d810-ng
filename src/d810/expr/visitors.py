"""Visitor pattern implementations for symbolic expression traversal.

This module provides visitors that traverse SymbolicExpression trees and convert
them to different representations (Z3 expressions, debug strings, etc.).

The key insight: SymbolicExpression is a pure tree structure with no backend
dependencies. Visitors convert it to specific representations:
- Z3VerificationVisitor → Z3 for theorem proving
- (Future) IDAVisitor → AstNode with IDA opcodes for runtime matching
- (Future) StringVisitor → Human-readable strings for debugging
"""

from __future__ import annotations

import typing
from typing import TYPE_CHECKING

try:
    import z3
    Z3_AVAILABLE = True
except ImportError:
    Z3_AVAILABLE = False

if TYPE_CHECKING:
    from d810.optimizers.dsl import SymbolicExpression


class Z3VerificationVisitor:
    """Visitor that converts SymbolicExpression to Z3 for verification/proving.

    This visitor walks a pure SymbolicExpression tree and builds equivalent
    Z3 symbolic expressions for theorem proving. It has NO dependencies on
    IDA Pro - it works entirely with platform-independent symbolic expressions.

    Example:
        >>> from d810.optimizers.dsl import Var
        >>> x, y = Var("x"), Var("y")
        >>> pattern = (x | y) - (x & y)  # Pure SymbolicExpression
        >>>
        >>> visitor = Z3VerificationVisitor()
        >>> z3_expr = visitor.visit(pattern)  # Convert to Z3
        >>> # z3_expr is now a z3.BitVecRef representing (x | y) - (x & y)
    """

    def __init__(self, bit_width: int = 32, var_map: dict[str, z3.BitVecRef] | None = None):
        """Initialize the Z3 verification visitor.

        Args:
            bit_width: Bit width for Z3 BitVec variables (default 32).
            var_map: Optional pre-created Z3 variables. If provided, the visitor
                    will use these instead of creating new ones. Useful when you
                    need to share variables across multiple expressions.
        """
        if not Z3_AVAILABLE:
            raise ImportError("Z3 is not installed. Install z3-solver to use Z3VerificationVisitor.")

        self.bit_width = bit_width
        self.var_map: dict[str, z3.BitVecRef] = var_map if var_map is not None else {}

    def visit(self, expr: SymbolicExpression) -> z3.BitVecRef:
        """Visit a SymbolicExpression and return the equivalent Z3 expression.

        Args:
            expr: The SymbolicExpression to visit.

        Returns:
            A Z3 BitVecRef representing the expression.

        Raises:
            ValueError: If the expression is None or invalid.
        """
        if expr is None:
            raise ValueError("Cannot visit None expression")

        if expr.is_leaf():
            return self._visit_leaf(expr)

        return self._visit_operation(expr)

    def _visit_leaf(self, expr: SymbolicExpression) -> z3.BitVecRef:
        """Visit a leaf node (variable or constant).

        Args:
            expr: The leaf SymbolicExpression.

        Returns:
            Z3 BitVec for variables, Z3 BitVecVal for concrete constants.
        """
        if expr.is_constant():
            # Concrete constant like Const("ONE", 1)
            return z3.BitVecVal(expr.value, self.bit_width)

        # Variable or pattern-matching constant like Var("x") or Const("c_1")
        if expr.name not in self.var_map:
            self.var_map[expr.name] = z3.BitVec(expr.name, self.bit_width)

        return self.var_map[expr.name]

    def _visit_operation(self, expr: SymbolicExpression) -> z3.BitVecRef:
        """Visit an operation node (binary/unary operation).

        Args:
            expr: The operation SymbolicExpression.

        Returns:
            Z3 expression representing the operation.

        Raises:
            ValueError: If the operation is unsupported.
        """
        # Recursively visit children
        left = self.visit(expr.left) if expr.left else None
        right = self.visit(expr.right) if expr.right else None

        # Map operation strings to Z3 operations
        match expr.operation:
            # Unary operations
            case "neg":
                return -left

            case "lnot":
                # Logical NOT: returns 1 if operand is 0, else 0
                return z3.If(
                    left == z3.BitVecVal(0, self.bit_width),
                    z3.BitVecVal(1, self.bit_width),
                    z3.BitVecVal(0, self.bit_width),
                )

            case "bnot":
                return ~left

            # Binary arithmetic operations
            case "add":
                return left + right

            case "sub":
                return left - right

            case "mul":
                return left * right

            case "udiv":
                return z3.UDiv(left, right)

            case "sdiv":
                return left / right

            case "umod":
                return z3.URem(left, right)

            case "smod":
                return left % right

            # Binary bitwise operations
            case "or":
                return left | right

            case "and":
                return left & right

            case "xor":
                return left ^ right

            # Shift operations
            case "shl":
                return left << right

            case "shr":
                return z3.LShR(left, right)  # Logical shift right

            case "sar":
                return left >> right  # Arithmetic shift right

            # Comparison operations (return 0 or 1)
            case "setnz":
                return z3.If(
                    left != z3.BitVecVal(0, self.bit_width),
                    z3.BitVecVal(1, self.bit_width),
                    z3.BitVecVal(0, self.bit_width),
                )

            case "setz":
                return z3.If(
                    left == z3.BitVecVal(0, self.bit_width),
                    z3.BitVecVal(1, self.bit_width),
                    z3.BitVecVal(0, self.bit_width),
                )

            case "setae":
                return z3.If(
                    z3.UGE(left, right),
                    z3.BitVecVal(1, self.bit_width),
                    z3.BitVecVal(0, self.bit_width),
                )

            case "setb":
                return z3.If(
                    z3.ULT(left, right),
                    z3.BitVecVal(1, self.bit_width),
                    z3.BitVecVal(0, self.bit_width),
                )

            case "seta":
                return z3.If(
                    z3.UGT(left, right),
                    z3.BitVecVal(1, self.bit_width),
                    z3.BitVecVal(0, self.bit_width),
                )

            case "setbe":
                return z3.If(
                    z3.ULE(left, right),
                    z3.BitVecVal(1, self.bit_width),
                    z3.BitVecVal(0, self.bit_width),
                )

            case "setg":
                return z3.If(
                    left > right,
                    z3.BitVecVal(1, self.bit_width),
                    z3.BitVecVal(0, self.bit_width),
                )

            case "setge":
                return z3.If(
                    left >= right,
                    z3.BitVecVal(1, self.bit_width),
                    z3.BitVecVal(0, self.bit_width),
                )

            case "setl":
                return z3.If(
                    left < right,
                    z3.BitVecVal(1, self.bit_width),
                    z3.BitVecVal(0, self.bit_width),
                )

            case "setle":
                return z3.If(
                    left <= right,
                    z3.BitVecVal(1, self.bit_width),
                    z3.BitVecVal(0, self.bit_width),
                )

            case _:
                raise ValueError(
                    f"Unsupported operation in Z3VerificationVisitor: {expr.operation}. "
                    f"Add support for this operation in visitors.py"
                )

    def get_variables(self) -> dict[str, z3.BitVecRef]:
        """Get all Z3 variables created during visitation.

        Returns:
            Dictionary mapping variable names to Z3 BitVecRef objects.
            Useful for adding constraints to the solver.
        """
        return self.var_map.copy()


def prove_equivalence(
    pattern: SymbolicExpression,
    replacement: SymbolicExpression,
    z3_vars: dict[str, z3.BitVecRef] | None = None,
    constraints: list[typing.Any] | None = None,
    bit_width: int = 32,
) -> tuple[bool, dict[str, int] | None]:
    """Prove that two SymbolicExpressions are semantically equivalent using Z3.

    This function uses the Z3VerificationVisitor to convert both expressions
    to Z3, then attempts to prove they are equivalent for all possible variable
    values (subject to any constraints).

    Args:
        pattern: The first SymbolicExpression (typically the pattern to match).
        replacement: The second SymbolicExpression (typically the replacement).
        z3_vars: Optional pre-created Z3 variables. If provided, these will be
                used for pattern constants and variables. If None, variables
                will be created automatically.
        constraints: Optional list of Z3 constraint expressions (BoolRef objects).
                    These constraints must hold for the equivalence to be valid.
        bit_width: Bit width for Z3 variables (default 32).

    Returns:
        A tuple of (is_equivalent, counterexample):
        - is_equivalent: True if proven equivalent, False otherwise.
        - counterexample: If not equivalent, a dict mapping variable names to
                         values that demonstrate the difference. None if equivalent.

    Example:
        >>> from d810.optimizers.dsl import Var
        >>> x, y = Var("x"), Var("y")
        >>> pattern = (x | y) - (x & y)
        >>> replacement = x ^ y
        >>> is_equiv, _ = prove_equivalence(pattern, replacement)
        >>> assert is_equiv  # These are mathematically equivalent
    """
    if not Z3_AVAILABLE:
        raise ImportError("Z3 is not installed. Install z3-solver to prove equivalence.")

    # Create visitor with optional pre-created variables
    visitor = Z3VerificationVisitor(bit_width=bit_width, var_map=z3_vars)

    try:
        pattern_z3 = visitor.visit(pattern)
        replacement_z3 = visitor.visit(replacement)
    except Exception as e:
        # Conversion failed - expressions are invalid or contain unsupported operations
        return False, None

    # Create solver and add constraints
    solver = z3.Solver()

    if constraints:
        for constraint in constraints:
            solver.add(constraint)

    # Prove equivalence by checking if inequality is unsatisfiable
    # If pattern != replacement has no solution, they are equivalent
    solver.add(pattern_z3 != replacement_z3)
    result = solver.check()

    if result == z3.unsat:
        # No counterexample exists - patterns are equivalent!
        return True, None

    if result == z3.sat:
        # Found a counterexample - patterns are NOT equivalent
        model = solver.model()
        counterexample = {}

        for name, z3_var in visitor.get_variables().items():
            value = model.eval(z3_var, model_completion=True)
            if hasattr(value, 'as_long'):
                counterexample[name] = value.as_long()
            else:
                counterexample[name] = str(value)

        return False, counterexample

    # Z3 returned unknown - cannot prove either way
    return False, None
