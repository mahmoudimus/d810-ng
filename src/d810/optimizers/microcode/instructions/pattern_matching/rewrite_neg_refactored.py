"""Refactored NEG (negation) pattern matching rules using the declarative DSL.

This module demonstrates rules involving constants and negation operations.
The DSL makes the two's complement relationship between BNOT and NEG obvious.
"""

from d810.optimizers.dsl import Var, Const, ONE
from d810.optimizers.rules import VerifiableRule

# Define symbolic variable
x = Var("x")


class NegFromBnotAdd(VerifiableRule):
    """Two's complement identity: ~x + 1 ≡ -x

    This is the fundamental definition of two's complement negation.
    To negate a number in two's complement:
    1. Flip all bits (bitwise NOT)
    2. Add 1

    This rule simplifies the verbose form into the concise negation operator.

    Verification:
        Automatically verified by Z3 to prove correctness for all 32-bit inputs.
    """

    name = "NegFromBnotAdd"
    description = "~x + 1 => -x (two's complement negation)"

    @property
    def pattern(self):
        """Pattern: ~x + 1"""
        return ~x + ONE

    @property
    def replacement(self):
        """Replacement: -x"""
        return -x


class BnotAddFromNeg(VerifiableRule):
    """Inverse of two's complement: -x ≡ ~x + 1

    This is the reverse transformation. Sometimes the expanded form is actually
    useful (e.g., when other optimizations can eliminate the +1).

    This demonstrates that rules can be bidirectional. The DSL and verification
    framework don't care about the direction - they just prove equivalence.

    Verification:
        Automatically verified by Z3 (should pass since it's the inverse of the above).
    """

    name = "BnotAddFromNeg"
    description = "-x => ~x + 1 (expand negation to two's complement form)"

    @property
    def pattern(self):
        """Pattern: -x"""
        return -x

    @property
    def replacement(self):
        """Replacement: ~x + 1"""
        return ~x + ONE


class NegIdentity(VerifiableRule):
    """Double negation identity: -(-x) ≡ x

    Negating a negation returns the original value.
    This is a simple algebraic identity that can simplify expressions.

    Verification:
        Automatically verified by Z3.
    """

    name = "NegIdentity"
    description = "-(-x) => x (double negation elimination)"

    @property
    def pattern(self):
        """Pattern: -(-x)"""
        return -(-x)

    @property
    def replacement(self):
        """Replacement: x"""
        return x


# Note how readable these rules are compared to manual AST construction!
# Compare:
#   OLD: AstNode(m_add, AstNode(m_bnot, AstLeaf("x")), AstConstant("1", 1))
#   NEW: ~x + ONE
#
# The new form is:
# - Immediately understandable
# - Easy to verify by inspection
# - Automatically verified by Z3
# - Self-documenting with proper mathematical notation
