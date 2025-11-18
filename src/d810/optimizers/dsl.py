"""A declarative DSL for defining optimization rules using symbolic expressions.

This module provides a high-level, declarative way to define optimization patterns
using Python's operator overloading. Instead of manually constructing AST trees,
rules can be written in a mathematical, self-documenting style.

Example:
    Instead of writing:
        AstNode(m_add, AstNode(m_bnot, AstLeaf("x")), AstConstant("1", 1))

    You can write:
        ~x + one

    This makes the intent clear and the code easier to verify for correctness.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from ida_hexrays import (
    m_add,
    m_and,
    m_bnot,
    m_mul,
    m_neg,
    m_or,
    m_shl,
    m_shr,
    m_sub,
    m_xor,
)

if TYPE_CHECKING:
    from d810.expr.ast import AstBase, AstNode


class SymbolicExpression:
    """A symbolic representation of a microcode expression tree.

    This class wraps an AstNode and provides operator overloading to build
    complex expressions using natural mathematical syntax. The underlying
    AstNode tree is constructed transparently.

    Attributes:
        node: The underlying AstNode representing this expression.
    """

    def __init__(self, node: AstBase):
        """Initialize a symbolic expression with an AST node.

        Args:
            node: The AST node (AstNode, AstLeaf, or AstConstant) to wrap.
        """
        self.node = node

    def __add__(self, other: SymbolicExpression) -> SymbolicExpression:
        """Addition: self + other -> m_add node."""
        from d810.expr.ast import AstNode
        return SymbolicExpression(AstNode(m_add, self.node, other.node))

    def __sub__(self, other: SymbolicExpression) -> SymbolicExpression:
        """Subtraction: self - other -> m_sub node."""
        from d810.expr.ast import AstNode
        return SymbolicExpression(AstNode(m_sub, self.node, other.node))

    def __xor__(self, other: SymbolicExpression) -> SymbolicExpression:
        """XOR: self ^ other -> m_xor node."""
        from d810.expr.ast import AstNode
        return SymbolicExpression(AstNode(m_xor, self.node, other.node))

    def __and__(self, other: SymbolicExpression) -> SymbolicExpression:
        """Bitwise AND: self & other -> m_and node."""
        from d810.expr.ast import AstNode
        return SymbolicExpression(AstNode(m_and, self.node, other.node))

    def __or__(self, other: SymbolicExpression) -> SymbolicExpression:
        """Bitwise OR: self | other -> m_or node."""
        from d810.expr.ast import AstNode
        return SymbolicExpression(AstNode(m_or, self.node, other.node))

    def __mul__(self, other: SymbolicExpression) -> SymbolicExpression:
        """Multiplication: self * other -> m_mul node."""
        from d810.expr.ast import AstNode
        return SymbolicExpression(AstNode(m_mul, self.node, other.node))

    def __lshift__(self, other: SymbolicExpression) -> SymbolicExpression:
        """Left shift: self << other -> m_shl node."""
        from d810.expr.ast import AstNode
        return SymbolicExpression(AstNode(m_shl, self.node, other.node))

    def __rshift__(self, other: SymbolicExpression) -> SymbolicExpression:
        """Right shift: self >> other -> m_shr node."""
        from d810.expr.ast import AstNode
        return SymbolicExpression(AstNode(m_shr, self.node, other.node))

    def __invert__(self) -> SymbolicExpression:
        """Bitwise NOT: ~self -> m_bnot node."""
        from d810.expr.ast import AstNode
        return SymbolicExpression(AstNode(m_bnot, self.node))

    def __neg__(self) -> SymbolicExpression:
        """Negation: -self -> m_neg node."""
        from d810.expr.ast import AstNode
        return SymbolicExpression(AstNode(m_neg, self.node))

    def __repr__(self) -> str:
        """Return a string representation of this expression."""
        return str(self.node)

    def __str__(self) -> str:
        """Return a string representation of this expression."""
        return str(self.node)


def Var(name: str) -> SymbolicExpression:
    """Create a symbolic variable with the given name.

    This factory function creates an AstLeaf (a variable in the pattern)
    and wraps it in a SymbolicExpression for operator overloading.

    Args:
        name: The name of the variable (e.g., "x", "y", "a", "b").

    Returns:
        A SymbolicExpression representing a pattern variable.

    Example:
        >>> x = Var("x")
        >>> y = Var("y")
        >>> pattern = x + y  # Represents: AstNode(m_add, AstLeaf("x"), AstLeaf("y"))
    """
    from d810.expr.ast import AstLeaf
    return SymbolicExpression(AstLeaf(name))


def Const(name: str, value: int | None = None) -> SymbolicExpression:
    """Create a symbolic constant with the given name and optional value.

    This factory function creates an AstConstant and wraps it in a
    SymbolicExpression. Constants can have specific values (for exact matching)
    or be unspecified (to match any constant in that position).

    Args:
        name: The name/identifier for this constant (e.g., "c1", "one").
        value: The optional concrete value for this constant. If None, matches any constant.

    Returns:
        A SymbolicExpression representing a constant in the pattern.

    Example:
        >>> one = Const("one", 1)
        >>> x = Var("x")
        >>> pattern = ~x + one  # Represents: ~x + 1 (two's complement negation)
    """
    from d810.expr.ast import AstConstant
    # AstConstant expects a value, so we use 0 as a default if None is provided
    # The actual matching logic should handle the "match any constant" case
    actual_value = value if value is not None else 0
    return SymbolicExpression(AstConstant(name, actual_value))


# Common symbolic constants for convenience
# These can be imported and used directly in rule definitions
ZERO = Const("0", 0)
ONE = Const("1", 1)
TWO = Const("2", 2)
NEGATIVE_ONE = Const("-1", -1)
