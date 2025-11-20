"""Self-verifying optimization rules using symbolic expressions and Z3.

This module provides base classes for creating optimization rules that can
automatically verify their own correctness using Z3 theorem proving. Rules
defined using the symbolic DSL can be mathematically proven to be correct.

The key innovation is that each rule carries its own correctness proof,
eliminating the need for manual test cases for every rule.
"""

from __future__ import annotations

import abc
from typing import Any, Dict, List

try:
    import z3
    Z3_AVAILABLE = True
except ImportError:
    Z3_AVAILABLE = False

from d810.conf.loggers import getLogger
from d810.expr.z3_utils import z3_prove_equivalence
from d810.optimizers.core import OptimizationContext
from d810.optimizers.dsl import SymbolicExpression

# Import the pattern matching rule base class for registry integration
# This will be imported lazily to avoid circular dependencies
_PatternMatchingRule = None

def _get_pattern_matching_rule():
    """Lazy import of PatternMatchingRule to avoid circular dependencies."""
    global _PatternMatchingRule
    if _PatternMatchingRule is None:
        try:
            from d810.optimizers.microcode.instructions.pattern_matching.handler import PatternMatchingRule
            _PatternMatchingRule = PatternMatchingRule
        except ImportError:
            # If we can't import it, use a dummy base class
            _PatternMatchingRule = object
    return _PatternMatchingRule

logger = getLogger(__name__)

# Global registry of all verifiable rules for automated testing
RULE_REGISTRY: List[VerifiableRule] = []


class SymbolicRule(abc.ABC):
    """A rule defined by symbolic, verifiable expressions.

    This abstract base class represents an optimization rule where both the
    pattern to match and the replacement are defined using the symbolic DSL.
    The rule can be verified for correctness using Z3.

    Subclasses must define the pattern and replacement as SymbolicExpression
    objects using Python's operator overloading for readability.
    """

    name: str = "UnnamedSymbolicRule"
    description: str = "No description"

    @property
    @abc.abstractmethod
    def pattern(self) -> SymbolicExpression:
        """The symbolic pattern to match.

        Returns:
            A SymbolicExpression representing the pattern to search for.

        Example:
            >>> from d810.optimizers.dsl import Var
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
            >>> from d810.optimizers.dsl import Var
            >>> x, y = Var("x"), Var("y")
            >>> return x ^ y
        """
        ...

    def verify(self) -> bool:
        """Proves that the pattern is equivalent to the replacement using Z3.

        This method converts both the pattern and replacement to Z3 expressions
        and attempts to prove they are semantically equivalent for all inputs.

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

        is_equivalent, counterexample = z3_prove_equivalence(
            self.pattern.node,
            self.replacement.node
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

    def apply(self, context: OptimizationContext, ins: "minsn_t") -> int:
        """Applies the symbolic rule to a single instruction.

        This method implements the pattern matching and replacement logic.
        It will be fully implemented as part of the pattern matching refactoring.

        Args:
            context: The optimization context.
            ins: The microcode instruction to potentially optimize.

        Returns:
            1 if the instruction was modified, 0 otherwise.
        """
        # This will be implemented as part of the pattern matching refactoring
        raise NotImplementedError(
            "SymbolicRule.apply() will be implemented in the pattern matching refactoring"
        )


class VerifiableRule(SymbolicRule):
    """A symbolic rule that can verify its own correctness with constraints.

    This class extends SymbolicRule to support rules that are only valid under
    certain conditions (constraints). For example, a rule might only be valid
    when a constant c2 equals ~c1.

    All subclasses are automatically registered in RULE_REGISTRY for batch testing.

    Class Variables:
        CONSTRAINTS: Optional list of runtime constraint functions.
                    Each function takes a match context dict and returns bool.
        DYNAMIC_CONSTS: Optional dict mapping constant names to compute functions.
                       Used for constants whose values depend on matched values.

    Example with constraints:
        >>> from d810.optimizers.dsl import when
        >>> class MyRule(VerifiableRule):
        ...     PATTERN = (x ^ Const("c_1")) + (x + Const("c_2"))
        ...     REPLACEMENT = x & y
        ...     CONSTRAINTS = [when.equal_mops("c_1", "c_2")]

    Example with dynamic constants:
        >>> class MyRule(VerifiableRule):
        ...     PATTERN = x + Const("c_2")
        ...     REPLACEMENT = x + DynamicConst("val_res", lambda ctx: ctx['c_2'].value - 1)
    """

    BIT_WIDTH = 32  # Default bit-width for Z3 verification

    # Override these in subclasses
    CONSTRAINTS: List = []  # Runtime constraints (list of callables)
    DYNAMIC_CONSTS: Dict[str, Any] = {}  # Dynamic constant generators

    def __init_subclass__(cls, **kwargs):
        """Automatically register any subclass for testing.

        This magic method is called whenever a class inherits from VerifiableRule.
        It instantiates the rule and adds it to the global registry.
        """
        super().__init_subclass__(**kwargs)
        # Only register concrete classes, not abstract ones
        if not isabstract(cls):
            try:
                RULE_REGISTRY.append(cls())
            except Exception as e:
                logger.warning(
                    f"Failed to register rule {cls.__name__}: {e}",
                    exc_info=True
                )

    def check_runtime_constraints(self, match_context: Dict[str, Any]) -> bool:
        """Check if all runtime constraints are satisfied for this match.

        This method evaluates the CONSTRAINTS list against the matched values.
        Each constraint is a callable that takes the match context and returns bool.

        Args:
            match_context: Dictionary mapping variable names to matched AstNodes/values.

        Returns:
            True if all constraints pass, False otherwise.

        Example:
            >>> # In a rule definition:
            >>> from d810.optimizers.dsl import when
            >>> CONSTRAINTS = [
            ...     when.equal_mops("c_1", "c_2"),
            ...     when.is_bnot("x_0", "bnot_x_0"),
            ... ]
        """
        if not hasattr(self, 'CONSTRAINTS') or not self.CONSTRAINTS:
            return True

        for constraint in self.CONSTRAINTS:
            try:
                if not constraint(match_context):
                    return False
            except (KeyError, AttributeError, TypeError) as e:
                logger.debug(
                    f"Constraint check failed for {self.name}: {e}"
                )
                return False

        return True

    def get_constraints(self, z3_vars: Dict[str, Any]) -> List[Any]:
        """Optional: Define Z3 constraints for this rule's validity.

        Some rules are only valid under certain conditions. For example, a rule
        might require that constant c2 equals ~c1. Override this method to
        specify such constraints.

        Note: For most rules, use the CONSTRAINTS class variable instead,
        which is checked at runtime. This method is for Z3 verification only.

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

    def verify(self) -> bool:
        """Proves that pattern ≡ replacement under the defined constraints.

        This enhanced verification:
        1. Extracts all symbolic variables from both pattern and replacement
        2. Creates Z3 BitVec variables for each
        3. Applies any rule-specific constraints
        4. Proves equivalence using Z3 SMT solver

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

        # Get AST nodes from symbolic expressions
        pattern_node = self.pattern.node
        replacement_node = self.replacement.node

        # Find all unique variable names (this will need to be adapted based on
        # how AstLeaf stores variable names - might be 'name' or another attribute)
        pattern_leaves = pattern_node.get_leaf_list()
        replacement_leaves = replacement_node.get_leaf_list()

        var_names = set()
        for leaf in pattern_leaves + replacement_leaves:
            if not leaf.is_constant() and hasattr(leaf, 'name'):
                var_names.add(leaf.name)

        # Create Z3 BitVec variables
        z3_vars = {name: z3.BitVec(name, self.BIT_WIDTH) for name in sorted(var_names)}

        # Get rule-specific constraints
        constraints = self.get_constraints(z3_vars)

        # Prove equivalence
        is_equivalent, counterexample = z3_prove_equivalence(
            pattern_node,
            replacement_node,
            z3_vars=z3_vars,
            constraints=constraints,
            bit_width=self.BIT_WIDTH
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

        logger.debug(f"Rule {self.name} verified successfully")
        return True


def isabstract(cls) -> bool:
    """Check if a class is abstract (has unimplemented abstract methods).

    Args:
        cls: The class to check.

    Returns:
        True if the class has any unimplemented abstract methods.
    """
    return bool(getattr(cls, "__abstractmethods__", None))
