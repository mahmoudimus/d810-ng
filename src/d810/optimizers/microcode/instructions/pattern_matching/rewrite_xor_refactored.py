"""Refactored XOR pattern matching rules using the declarative DSL.

This module demonstrates the new approach to defining optimization rules:
- Declarative syntax using operator overloading
- Self-documenting code that reads like mathematics
- Automatic verification using Z3
- No manual AST tree construction

Compare this to the original rewrite_xor.py to see the dramatic improvement
in readability and maintainability.
"""

from d810.optimizers.dsl import Var, Const
from d810.optimizers.rules import VerifiableRule

# Define symbolic variables once for the module
x = Var("x")
y = Var("y")
two = Const("2", 2)


class XorFromOrAndSub(VerifiableRule):
    """Hacker's Delight identity: (x | y) - (x & y) ≡ x ^ y

    This rule recognizes a common obfuscation pattern where XOR is implemented
    using OR, AND, and subtraction. The pattern exploits the identity:
        x ^ y = (x | y) - (x & y)

    This is a well-known bit manipulation trick from "Hacker's Delight" by
    Henry S. Warren Jr.

    Verification:
        This rule is automatically verified by Z3 to prove the transformation
        is semantically equivalent for all 32-bit inputs.
    """

    name = "XorFromOrAndSub"
    description = "(x | y) - (x & y) => x ^ y"

    @property
    def pattern(self):
        """Pattern: (x | y) - (x & y)"""
        return (x | y) - (x & y)

    @property
    def replacement(self):
        """Replacement: x ^ y"""
        return x ^ y


class XorFromMulOrAdd(VerifiableRule):
    """Hacker's Delight identity: 2*(x | y) - (x + y) ≡ x ^ y

    This rule recognizes another XOR obfuscation using multiplication, OR, and addition.
    The identity is:
        x ^ y = 2*(x | y) - (x + y)

    This works because:
    - x + y counts each common bit (where both are 1) twice
    - 2*(x | y) counts all set bits in either operand twice
    - The difference gives bits set in exactly one operand

    Verification:
        Automatically verified by Z3 for correctness.
    """

    name = "XorFromMulOrAdd"
    description = "2*(x | y) - (x + y) => x ^ y"

    @property
    def pattern(self):
        """Pattern: 2*(x | y) - (x + y)"""
        return two * (x | y) - (x + y)

    @property
    def replacement(self):
        """Replacement: x ^ y"""
        return x ^ y


class XorFromAddMulOr(VerifiableRule):
    """Hacker's Delight identity: (x + y) - 2*(x & y) ≡ x ^ y

    Yet another XOR obfuscation pattern. This one uses:
        x ^ y = (x + y) - 2*(x & y)

    The reasoning:
    - x + y counts common bits (both 1) twice, unique bits once
    - 2*(x & y) counts common bits twice
    - Subtracting leaves only the unique bits (XOR)

    Verification:
        Automatically verified by Z3 for correctness.
    """

    name = "XorFromAddMulOr"
    description = "(x + y) - 2*(x & y) => x ^ y"

    @property
    def pattern(self):
        """Pattern: (x + y) - 2*(x & y)"""
        return (x + y) - two * (x & y)

    @property
    def replacement(self):
        """Replacement: x ^ y"""
        return x ^ y


# Example of how to define a rule with constraints
# (This is a hypothetical example, not from the original code)
class XorSymmetry(VerifiableRule):
    """Demonstrates XOR symmetry: x ^ y ≡ y ^ x

    This trivial identity demonstrates how the verification framework works.
    XOR is commutative, so swapping operands doesn't change the result.

    This could be useful for canonicalization (ensuring a consistent form).
    """

    name = "XorSymmetry"
    description = "x ^ y => y ^ x (XOR is commutative)"

    @property
    def pattern(self):
        """Pattern: x ^ y"""
        return x ^ y

    @property
    def replacement(self):
        """Replacement: y ^ x"""
        return y ^ x


# When this module is imported, all VerifiableRule subclasses are automatically
# registered in RULE_REGISTRY for batch testing. No manual registration needed!
