"""Visitor pattern implementations for AST traversal.

This module provides visitors that traverse AST trees and convert them
to different representations (Z3 expressions, IDA opcodes, debug strings, etc.).
"""

from __future__ import annotations

import typing
from typing import Any

try:
    import z3
    Z3_AVAILABLE = True
except ImportError:
    Z3_AVAILABLE = False

import d810.opcodes as opc
from d810.expr.ast import AstLeaf, AstNode


class Z3Visitor:
    """Visitor that converts AST to Z3 expressions for verification.

    This visitor walks an AST tree (created by the DSL) and builds equivalent
    Z3 symbolic expressions. Each variable/constant becomes a Z3 BitVec, and
    operations are mapped to Z3 operations.

    Example:
        >>> from d810.optimizers.dsl import Var
        >>> x, y = Var("x"), Var("y")
        >>> pattern = (x | y) - (x & y)  # Creates AST
        >>>
        >>> visitor = Z3Visitor()
        >>> z3_expr = visitor.visit(pattern.node)  # Convert to Z3
        >>> # z3_expr is now: (x | y) - (x & y) in Z3's representation
    """

    def __init__(self, bit_width: int = 32, var_map: dict[str, z3.BitVecRef] | None = None):
        """Initialize the Z3 visitor.

        Args:
            bit_width: Bit width for Z3 BitVec variables (default 32).
            var_map: Optional pre-created Z3 variables. If provided, the visitor
                    will use these instead of creating new ones.
        """
        if not Z3_AVAILABLE:
            raise ImportError("Z3 is not installed. Install z3-solver to use Z3Visitor.")

        self.bit_width = bit_width
        self.var_map: dict[str, z3.BitVecRef] = var_map if var_map is not None else {}

    def visit(self, ast: AstNode | AstLeaf) -> z3.BitVecRef:
        """Visit an AST node and return the equivalent Z3 expression.

        Args:
            ast: The AST node to visit (AstNode or AstLeaf).

        Returns:
            A Z3 BitVecRef representing the expression.

        Raises:
            ValueError: If the AST is None or invalid.
        """
        if ast is None:
            raise ValueError("Cannot visit None AST")

        if ast.is_leaf():
            return self._visit_leaf(typing.cast(AstLeaf, ast))

        return self._visit_node(typing.cast(AstNode, ast))

    def _visit_leaf(self, leaf: AstLeaf) -> z3.BitVecRef:
        """Visit a leaf node (variable or constant).

        Args:
            leaf: The AstLeaf to visit.

        Returns:
            Z3 BitVec for variables, Z3 BitVecVal for concrete constants.
        """
        if leaf.is_constant():
            # Check if this is a pattern-matching constant (no concrete value)
            if hasattr(leaf, 'expected_value') and leaf.expected_value is None:
                # Symbolic constant like Const("c_1") - treat as variable
                if leaf.name not in self.var_map:
                    self.var_map[leaf.name] = z3.BitVec(leaf.name, self.bit_width)
                return self.var_map[leaf.name]

            # Concrete constant like Const("ONE", 1)
            return z3.BitVecVal(leaf.value, self.bit_width)

        # Regular variable like Var("x")
        if leaf.name not in self.var_map:
            self.var_map[leaf.name] = z3.BitVec(leaf.name, self.bit_width)

        return self.var_map[leaf.name]

    def _visit_node(self, node: AstNode) -> z3.BitVecRef:
        """Visit an operation node (binary/unary operation).

        Args:
            node: The AstNode to visit.

        Returns:
            Z3 expression representing the operation.

        Raises:
            ValueError: If the opcode is unsupported.
        """
        # Recursively visit children
        left = self.visit(node.left) if node.left else None
        right = self.visit(node.right) if node.right else None

        # Map opcode to Z3 operation
        match node.opcode:
            # Unary operations
            case opc.M_NEG:
                return -left

            case opc.M_LNOT:
                # Logical NOT: returns 1 if operand is 0, else 0
                return z3.If(
                    left == z3.BitVecVal(0, self.bit_width),
                    z3.BitVecVal(1, self.bit_width),
                    z3.BitVecVal(0, self.bit_width),
                )

            case opc.M_BNOT:
                return ~left

            # Binary arithmetic operations
            case opc.M_ADD:
                return left + right

            case opc.M_SUB:
                return left - right

            case opc.M_MUL:
                return left * right

            case opc.M_UDIV:
                return z3.UDiv(left, right)

            case opc.M_SDIV:
                return left / right

            case opc.M_UMOD:
                return z3.URem(left, right)

            case opc.M_SMOD:
                return left % right

            # Binary bitwise operations
            case opc.M_OR:
                return left | right

            case opc.M_AND:
                return left & right

            case opc.M_XOR:
                return left ^ right

            # Shift operations
            case opc.M_SHL:
                return left << right

            case opc.M_SHR:
                return z3.LShR(left, right)  # Logical shift right

            case opc.M_SAR:
                return left >> right  # Arithmetic shift right

            # Comparison operations (return 0 or 1)
            case opc.M_SETNZ:
                return z3.If(
                    left != z3.BitVecVal(0, self.bit_width),
                    z3.BitVecVal(1, self.bit_width),
                    z3.BitVecVal(0, self.bit_width),
                )

            case opc.M_SETZ:
                return z3.If(
                    left == z3.BitVecVal(0, self.bit_width),
                    z3.BitVecVal(1, self.bit_width),
                    z3.BitVecVal(0, self.bit_width),
                )

            case opc.M_SETAE:
                return z3.If(
                    z3.UGE(left, right),
                    z3.BitVecVal(1, self.bit_width),
                    z3.BitVecVal(0, self.bit_width),
                )

            case opc.M_SETB:
                return z3.If(
                    z3.ULT(left, right),
                    z3.BitVecVal(1, self.bit_width),
                    z3.BitVecVal(0, self.bit_width),
                )

            case opc.M_SETA:
                return z3.If(
                    z3.UGT(left, right),
                    z3.BitVecVal(1, self.bit_width),
                    z3.BitVecVal(0, self.bit_width),
                )

            case opc.M_SETBE:
                return z3.If(
                    z3.ULE(left, right),
                    z3.BitVecVal(1, self.bit_width),
                    z3.BitVecVal(0, self.bit_width),
                )

            case opc.M_SETG:
                return z3.If(
                    left > right,
                    z3.BitVecVal(1, self.bit_width),
                    z3.BitVecVal(0, self.bit_width),
                )

            case opc.M_SETGE:
                return z3.If(
                    left >= right,
                    z3.BitVecVal(1, self.bit_width),
                    z3.BitVecVal(0, self.bit_width),
                )

            case opc.M_SETL:
                return z3.If(
                    left < right,
                    z3.BitVecVal(1, self.bit_width),
                    z3.BitVecVal(0, self.bit_width),
                )

            case opc.M_SETLE:
                return z3.If(
                    left <= right,
                    z3.BitVecVal(1, self.bit_width),
                    z3.BitVecVal(0, self.bit_width),
                )

            case _:
                raise ValueError(
                    f"Unsupported opcode in Z3Visitor: {node.opcode}. "
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
    pattern_ast: AstNode | AstLeaf,
    replacement_ast: AstNode | AstLeaf,
    z3_vars: dict[str, z3.BitVecRef] | None = None,
    constraints: list[Any] | None = None,
    bit_width: int = 32,
) -> tuple[bool, dict[str, int] | None]:
    """Prove that two AST expressions are semantically equivalent using Z3.

    This function uses the Z3Visitor to convert both ASTs to Z3 expressions,
    then attempts to prove they are equivalent for all possible variable values.

    Args:
        pattern_ast: The first AST (typically the pattern to match).
        replacement_ast: The second AST (typically the replacement).
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
        >>> is_equiv, _ = prove_equivalence(pattern.node, replacement.node)
        >>> assert is_equiv  # These are mathematically equivalent
    """
    if not Z3_AVAILABLE:
        raise ImportError("Z3 is not installed. Install z3-solver to prove equivalence.")

    # Create visitor with optional pre-created variables
    visitor = Z3Visitor(bit_width=bit_width, var_map=z3_vars)

    try:
        pattern_z3 = visitor.visit(pattern_ast)
        replacement_z3 = visitor.visit(replacement_ast)
    except Exception as e:
        # Conversion failed - ASTs are invalid or contain unsupported operations
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
