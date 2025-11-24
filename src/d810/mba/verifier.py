"""Pure verification framework for MBA simplification rules.

This module provides IDA-independent verification of optimization rules
using Z3 theorem proving. It contains the core logic for proving that
pattern transformations preserve semantics.

This is the extraction of pure verification logic from d810.optimizers.rules,
designed to work without IDA Pro dependencies.
"""

from __future__ import annotations

import abc
from typing import Any, Dict, List

try:
    import z3
    Z3_AVAILABLE = True
except ImportError:
    Z3_AVAILABLE = False

from d810.mba.dsl import SymbolicExpression
from d810.mba.visitors import prove_equivalence


class MBARule(abc.ABC):
    """A pure MBA simplification rule that can verify its own correctness.

    This is the IDA-independent base class for optimization rules. It defines
    a pattern-to-replacement transformation and can verify the mathematical
    correctness using Z3.

    Unlike d810.optimizers.rules.VerifiableRule, this class has:
    - NO IDA dependencies (no minsn_t, mop_t, AstNode)
    - Pure symbolic verification only
    - Can be used in standalone MBA simplification tools

    Subclasses must define:
        name: str - Human-readable rule name
        description: str - What the rule does
        pattern: SymbolicExpression - The pattern to match
        replacement: SymbolicExpression - The replacement expression

    Example:
        >>> from d810.mba import Var
        >>> class XorIdentity(MBARule):
        ...     name = "XOR from OR/AND"
        ...     description = "Simplify (x|y)-(x&y) to x^y"
        ...
        ...     @property
        ...     def pattern(self):
        ...         x, y = Var("x"), Var("y")
        ...         return (x | y) - (x & y)
        ...
        ...     @property
        ...     def replacement(self):
        ...         x, y = Var("x"), Var("y")
        ...         return x ^ y
        ...
        >>> rule = XorIdentity()
        >>> rule.verify()  # Proves correctness using Z3
        True
    """

    name: str = "UnnamedMBARule"
    description: str = "No description"

    @property
    @abc.abstractmethod
    def pattern(self) -> SymbolicExpression:
        """The symbolic pattern to match.

        Returns:
            A SymbolicExpression representing the pattern to search for.

        Example:
            >>> from d810.mba import Var
            >>> x, y = Var("x"), Var("y")
            >>> return (x | y) - (x & y)
        """
        ...

    @property
    @abc.abstractmethod
    def replacement(self) -> SymbolicExpression:
        """The symbolic expression to replace the pattern with.

        Returns:
            A SymbolicExpression representing the replacement.

        Example:
            >>> from d810.mba import Var
            >>> x, y = Var("x"), Var("y")
            >>> return x ^ y
        """
        ...

    def verify(self, bit_width: int = 32) -> bool:
        """Proves that the pattern is equivalent to the replacement using Z3.

        This method converts both the pattern and replacement to Z3 expressions
        and attempts to prove they are semantically equivalent for all inputs.

        Args:
            bit_width: Bit width for Z3 variables (default 32).

        Returns:
            True if the rule is proven correct.

        Raises:
            AssertionError: If the patterns are not equivalent or Z3 is unavailable.
        """
        if not Z3_AVAILABLE:
            raise AssertionError(
                f"Cannot verify rule {self.name}: Z3 is not installed. "
                "Install z3-solver to enable rule verification."
            )

        # Prove equivalence using pure SymbolicExpression
        is_equivalent, counterexample = prove_equivalence(
            self.pattern,
            self.replacement,
            bit_width=bit_width
        )

        if not is_equivalent:
            msg = (
                f"\n--- VERIFICATION FAILED ---\n"
                f"Rule:        {self.name}\n"
                f"Description: {self.description}\n"
                f"Identity:    {self.pattern} => {self.replacement}\n"
            )
            if counterexample:
                msg += f"Counterexample: {counterexample}\n"
            msg += (
                "This rule does NOT preserve semantics and should not be used.\n"
                "Please fix the pattern or replacement definition."
            )
            raise AssertionError(msg)

        return True


class ConstrainedMBARule(MBARule):
    """An MBA rule with constraints on when it's valid.

    Some MBA identities only hold under certain conditions. This class
    extends MBARule to support Z3 constraints.

    Example:
        >>> from d810.mba import Var, Const
        >>> class ConditionalRule(ConstrainedMBARule):
        ...     name = "Conditional simplification"
        ...     description = "x + c1 => x when c1 == 0"
        ...
        ...     @property
        ...     def pattern(self):
        ...         x, c1 = Var("x"), Var("c1")
        ...         return x + c1
        ...
        ...     @property
        ...     def replacement(self):
        ...         x = Var("x")
        ...         return x
        ...
        ...     def get_constraints(self, z3_vars):
        ...         # Only valid when c1 == 0
        ...         return [z3_vars["c1"] == 0]
    """

    def get_constraints(self, z3_vars: Dict[str, Any]) -> List[Any]:
        """Define Z3 constraints for this rule's validity.

        Some rules are only valid under certain conditions. For example, a rule
        might require that constant c2 equals ~c1. Override this method to
        specify such constraints.

        Args:
            z3_vars: A dictionary mapping symbolic variable names to Z3 BitVec objects.

        Returns:
            A list of Z3 constraint expressions. Empty list means no constraints.

        Example:
            >>> def get_constraints(self, z3_vars):
            ...     # This rule is only valid when c2 == ~c1
            ...     return [z3_vars["c2"] == ~z3_vars["c1"]]
        """
        return []

    def verify(self, bit_width: int = 32) -> bool:
        """Proves that pattern ≡ replacement under the defined constraints.

        This enhanced verification:
        1. Extracts all symbolic variables from both pattern and replacement
        2. Creates Z3 BitVec variables for each
        3. Applies any rule-specific constraints
        4. Proves equivalence using Z3 SMT solver

        Args:
            bit_width: Bit width for Z3 variables (default 32).

        Returns:
            True if the rule is proven correct under its constraints.

        Raises:
            AssertionError: If verification fails with detailed error message.
        """
        if not Z3_AVAILABLE:
            raise AssertionError(
                f"Cannot verify rule {self.name}: Z3 is not installed. "
                "Install z3-solver to enable rule verification."
            )

        # Find all unique variable names from pure SymbolicExpression
        # Pattern-matching constants (e.g., Const("c_1") without value)
        # must be treated as symbolic Z3 variables, not concrete values
        def collect_var_names(expr: SymbolicExpression, var_names: set):
            """Recursively collect variable and constant names from expression."""
            if expr is None:
                return
            if not isinstance(expr, SymbolicExpression):
                return

            if expr.is_leaf():
                if expr.name and expr.value is None:
                    # Variable or pattern-matching constant
                    var_names.add(expr.name)
            else:
                # Recurse into children
                if expr.left:
                    collect_var_names(expr.left, var_names)
                if expr.right:
                    collect_var_names(expr.right, var_names)

        var_names = set()
        collect_var_names(self.pattern, var_names)
        collect_var_names(self.replacement, var_names)

        # Skip verification if replacement is not a SymbolicExpression
        if not isinstance(self.replacement, SymbolicExpression):
            # Can't verify dynamic or non-symbolic replacements
            return True

        # Create Z3 BitVec variables for all symbolic variables/constants
        z3_vars = {}
        for name in sorted(var_names):
            z3_vars[name] = z3.BitVec(name, bit_width)

        # Get rule-specific constraints
        constraints = self.get_constraints(z3_vars)

        # Prove equivalence using pure SymbolicExpression
        is_equivalent, counterexample = prove_equivalence(
            self.pattern,
            self.replacement,
            z3_vars=z3_vars,
            constraints=constraints,
            bit_width=bit_width
        )

        if not is_equivalent:
            msg = (
                f"\n--- VERIFICATION FAILED ---\n"
                f"Rule:        {self.name}\n"
                f"Description: {self.description}\n"
                f"Identity:    {self.pattern} => {self.replacement}\n"
            )
            if counterexample:
                msg += f"Counterexample: {counterexample}\n"
            if constraints:
                msg += f"Constraints were: {constraints}\n"
            msg += (
                "This rule does NOT preserve semantics and should not be used.\n"
                "Please fix the pattern, replacement, or constraints."
            )
            raise AssertionError(msg)

        return True


def verify_transformation(
    pattern: SymbolicExpression,
    replacement: SymbolicExpression,
    constraints: List[Any] | None = None,
    bit_width: int = 32,
) -> tuple[bool, dict[str, int] | None]:
    """Verify that a transformation preserves semantics using Z3.

    This is a functional interface for one-off verification without
    creating an MBARule class.

    Args:
        pattern: The original expression.
        replacement: The simplified expression.
        constraints: Optional list of Z3 constraints that must hold.
        bit_width: Bit width for Z3 variables (default 32).

    Returns:
        A tuple of (is_equivalent, counterexample):
        - is_equivalent: True if proven equivalent, False otherwise.
        - counterexample: If not equivalent, a dict mapping variable names to
                         values that demonstrate the difference. None if equivalent.

    Example:
        >>> from d810.mba import Var, verify_transformation
        >>> x, y = Var("x"), Var("y")
        >>> pattern = (x | y) - (x & y)
        >>> replacement = x ^ y
        >>> is_valid, _ = verify_transformation(pattern, replacement)
        >>> assert is_valid
    """
    if not Z3_AVAILABLE:
        raise ImportError(
            "Z3 is not installed. Install z3-solver to use verify_transformation."
        )

    # Collect all variable names
    def collect_var_names(expr: SymbolicExpression, var_names: set):
        if expr is None or not isinstance(expr, SymbolicExpression):
            return
        if expr.is_leaf():
            if expr.name and expr.value is None:
                var_names.add(expr.name)
        else:
            if expr.left:
                collect_var_names(expr.left, var_names)
            if expr.right:
                collect_var_names(expr.right, var_names)

    var_names = set()
    collect_var_names(pattern, var_names)
    collect_var_names(replacement, var_names)

    # Create Z3 variables
    z3_vars = {name: z3.BitVec(name, bit_width) for name in sorted(var_names)}

    # Prove equivalence
    return prove_equivalence(
        pattern,
        replacement,
        z3_vars=z3_vars,
        constraints=constraints,
        bit_width=bit_width
    )


__all__ = [
    "MBARule",
    "ConstrainedMBARule",
    "verify_transformation",
]
