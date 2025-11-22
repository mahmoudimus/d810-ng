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

# Try to import IDA constants, fall back to mock values for unit testing
try:
    from ida_hexrays import (
        m_add,
        m_and,
        m_bnot,
        m_mul,
        m_neg,
        m_or,
        m_sar,
        m_shl,
        m_shr,
        m_sub,
        m_xor,
    )
except ImportError:
    # Mock IDA constants for unit testing without IDA Pro
    # These are placeholder opcodes that allow the DSL to be imported.
    # The actual values don't matter for Z3 verification - only the symbolic structure.
    m_add = 0
    m_and = 1
    m_bnot = 2
    m_mul = 3
    m_neg = 4
    m_or = 5
    m_sar = 6
    m_shl = 7
    m_shr = 8
    m_sub = 9
    m_xor = 10

if TYPE_CHECKING:
    from d810.expr.ast import AstBase, AstNode
    from d810.optimizers.constraints import ConstraintExpr


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

    def sar(self, other: SymbolicExpression) -> SymbolicExpression:
        """Arithmetic right shift: self.sar(other) -> m_sar node."""
        from d810.expr.ast import AstNode
        return SymbolicExpression(AstNode(m_sar, self.node, other.node))

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

    def __eq__(self, other: SymbolicExpression) -> ConstraintExpr:
        """Equality constraint: self == other.

        NOTE: This overrides Python's default equality to return a ConstraintExpr
        instead of bool. This allows writing declarative constraints like:
            val_res == c2 - ONE

        For object identity comparison, use `is` instead.

        Args:
            other: The right-hand side of the equality

        Returns:
            An EqualityConstraint that can be used in CONSTRAINTS list
        """
        from d810.optimizers.constraints import EqualityConstraint
        return EqualityConstraint(self, other)


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
    # Pass value as-is (including None for pattern-matching constants)
    # None = pattern-matching constant (symbolic)
    # int = concrete constant for exact matching
    return SymbolicExpression(AstConstant(name, value))


# Common symbolic constants for convenience
# These can be imported and used directly in rule definitions
ZERO = Const("0", 0)
ONE = Const("1", 1)
TWO = Const("2", 2)
NEGATIVE_ONE = Const("-1", -1)


class DynamicConst:
    """A constant whose value is computed dynamically at match time.

    This allows rules to compute new constant values based on matched
    constants in the pattern. For example, a rule might need to compute
    `c2 - 1` when it matches `c2`.

    Attributes:
        name: The name/identifier for this dynamic constant.
        compute: A function that takes the match context and returns the value.
        size_from: Optional variable name to copy the size from (default: use context size).

    Example:
        >>> # Rule that replaces pattern with c2 - 1
        >>> REPLACEMENT = x + DynamicConst("val_res", lambda ctx: ctx['c2'].value - 1)
    """

    def __init__(self, name: str, compute, size_from: str | None = None):
        """Initialize a dynamic constant.

        Args:
            name: The name for this constant in the replacement.
            compute: A callable that takes the match context dict and returns an int.
            size_from: Optional variable name to get the size from (e.g., "x_0").
        """
        self.name = name
        self.compute = compute
        self.size_from = size_from
        # Wrap in SymbolicExpression for operator overloading
        from d810.expr.ast import AstConstant
        # Use 0 as placeholder - actual value computed at match time
        self._placeholder = SymbolicExpression(AstConstant(name, 0))

    @property
    def node(self):
        """Expose the placeholder's node for Z3 verification."""
        return self._placeholder.node

    def __add__(self, other):
        return self._placeholder + other

    def __sub__(self, other):
        return self._placeholder - other

    def __xor__(self, other):
        return self._placeholder ^ other

    def __and__(self, other):
        return self._placeholder & other

    def __or__(self, other):
        return self._placeholder | other

    def __mul__(self, other):
        return self._placeholder * other

    def __radd__(self, other):
        return other + self._placeholder

    def __rsub__(self, other):
        return other - self._placeholder

    def __rxor__(self, other):
        return other ^ self._placeholder

    def __rand__(self, other):
        return other & self._placeholder

    def __ror__(self, other):
        return other | self._placeholder

    def __rmul__(self, other):
        return other * self._placeholder


class ConstraintPredicate:
    """Helper for defining common constraint predicates.

    This class provides factory methods for creating common constraint
    checks that rules need to perform on matched values.

    Example:
        >>> from d810.optimizers.dsl import when
        >>> CONSTRAINTS = [
        ...     when.equal_mops("c_1", "c_2"),  # c_1 value == c_2 value
        ...     when.is_bnot("c_1", "c_2"),     # c_1 == ~c_2
        ... ]
    """

    @staticmethod
    def equal_mops(var1: str, var2: str, ignore_size: bool = True):
        """Check that two matched operands have equal values.

        Args:
            var1: Name of first variable in the match context.
            var2: Name of second variable in the match context.
            ignore_size: If True, compare values ignoring operand size.

        Returns:
            A constraint function that checks equality.

        Example:
            >>> # Rule is only valid when c_1 value equals c_2 value
            >>> CONSTRAINTS = [when.equal_mops("c_1", "c_2")]
        """
        def check(ctx):
            from d810.hexrays.hexrays_helpers import equal_mops_ignore_size
            if var1 not in ctx or var2 not in ctx:
                return False
            if ignore_size:
                return equal_mops_ignore_size(ctx[var1].mop, ctx[var2].mop)
            else:
                return ctx[var1].mop == ctx[var2].mop
        return check

    @staticmethod
    def is_bnot(var1: str, var2: str):
        """Check that var1 == ~var2 (bitwise NOT relationship).

        Args:
            var1: Name of first variable.
            var2: Name of second variable (should be bitwise NOT of var1).

        Returns:
            A constraint function that checks the NOT relationship.

        Example:
            >>> # Rule is only valid when c_1 == ~c_2
            >>> CONSTRAINTS = [when.is_bnot("c_1", "c_2")]
        """
        def check(ctx):
            from d810.hexrays.hexrays_helpers import equal_bnot_mop
            if var1 not in ctx or var2 not in ctx:
                return False
            return equal_bnot_mop(ctx[var1].mop, ctx[var2].mop)
        return check

    @staticmethod
    def const_equals(var: str, value: int):
        """Check that a matched constant has a specific value.

        Args:
            var: Name of the constant variable.
            value: The expected value.

        Returns:
            A constraint function that checks the value.

        Example:
            >>> # Rule is only valid when c_1 equals 0xFF
            >>> CONSTRAINTS = [when.const_equals("c_1", 0xFF)]
        """
        def check(ctx):
            if var not in ctx:
                return False
            return ctx[var].value == value
        return check

    @staticmethod
    def const_satisfies(var: str, predicate):
        """Check that a matched constant satisfies a custom predicate.

        Args:
            var: Name of the constant variable.
            predicate: A function that takes an integer and returns bool.

        Returns:
            A constraint function that checks the predicate.

        Example:
            >>> # Rule is only valid when (val_fe + 2) & mask == 0
            >>> from d810.hexrays.hexrays_helpers import AND_TABLE
            >>> def check_val_fe(ctx):
            ...     val = ctx['val_fe'].value
            ...     size = ctx['val_fe'].size
            ...     return (val + 2) & AND_TABLE[size] == 0
            >>> CONSTRAINTS = [check_val_fe]
        """
        def check(ctx):
            if var not in ctx:
                return False
            return predicate(ctx[var].value)
        return check

    @staticmethod
    def bit_mask_check(var: str, mask_var: str, expected: int = 0):
        """Check that (var & mask) equals expected value.

        Args:
            var: Name of the variable to mask.
            mask_var: Name of the mask variable.
            expected: Expected result of the AND operation.

        Returns:
            A constraint function that checks the masked value.

        Example:
            >>> # Check that c_1 & 0xFF == c_2
            >>> CONSTRAINTS = [
            ...     lambda ctx: (ctx['c_1'].value & 0xFF) == ctx['c_2'].value
            ... ]
        """
        def check(ctx):
            if var not in ctx or mask_var not in ctx:
                return False
            return (ctx[var].value & ctx[mask_var].value) == expected
        return check


# Create a singleton instance for convenient access
when = ConstraintPredicate()
