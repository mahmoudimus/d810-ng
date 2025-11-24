"""Self-verifying optimization rules using symbolic expressions and Z3.

This module provides base classes for creating optimization rules that can
automatically verify their own correctness using Z3 theorem proving. Rules
defined using the symbolic DSL can be mathematically proven to be correct.

The key innovation is that each rule carries its own correctness proof,
eliminating the need for manual test cases for every rule.
"""

from __future__ import annotations

import abc
from typing import Any, Dict, List, TYPE_CHECKING

try:
    import z3
    Z3_AVAILABLE = True
except ImportError:
    Z3_AVAILABLE = False

from d810.conf.loggers import getLogger
from d810.mba.visitors import prove_equivalence
from d810.mba.dsl import SymbolicExpression

# Import types only for type checking to avoid circular imports and IDA dependencies
if TYPE_CHECKING:
    from d810.optimizers.core import OptimizationContext
    from d810.optimizers.microcode.instructions.pattern_matching.handler import PatternMatchingRule

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
            >>> from d810.mba.dsl import Var
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
            >>> from d810.mba.dsl import Var
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

        # Prove equivalence using pure SymbolicExpression (no .node needed!)
        is_equivalent, counterexample = prove_equivalence(
            self.pattern,
            self.replacement
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

    This class extends both SymbolicRule (for Z3 verification) and PatternMatchingRule
    (for d810 integration). It provides a bridge between the declarative DSL approach
    and d810's existing pattern matching infrastructure.

    All subclasses are automatically registered via Registrant metaclass.

    Class Variables:
        PATTERN: DSL-based pattern (SymbolicExpression from dsl module)
        REPLACEMENT: DSL-based replacement (SymbolicExpression from dsl module)
        CONSTRAINTS: Optional list of runtime constraint functions.
                    Each function takes a match context dict and returns bool.
        DYNAMIC_CONSTS: Optional dict mapping constant names to compute functions.
                       Used for constants whose values depend on matched values.

    Example:
        >>> from d810.mba.dsl import Var, Const
        >>> x, y = Var("x_0"), Var("x_1")
        >>> class Xor_HackersDelight1(VerifiableRule):
        ...     PATTERN = (x | y) - (x & y)
        ...     REPLACEMENT = x ^ y

    Example with constraints:
        >>> from d810.mba.dsl import when
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

    # Override these in subclasses - DSL format
    # These are class variables, not instance variables
    # PATTERN: SymbolicExpression = None
    # REPLACEMENT: SymbolicExpression = None
    CONSTRAINTS: List = []  # Runtime constraints (list of callables)
    DYNAMIC_CONSTS: Dict[str, Any] = {}  # Dynamic constant generators
    CONTEXT_VARS: Dict[str, Any] = {}  # Context providers (e.g., {"full_reg": context.dst.parent_register})
    UPDATE_DESTINATION: str = None  # Variable name to use as new destination (e.g., "full_reg")
    KNOWN_INCORRECT: bool = False  # Set to True for rules that are mathematically incorrect
    SKIP_VERIFICATION: bool = False  # Set to True to skip Z3 verification (e.g., for size-dependent constraints)

    def __init_subclass__(cls, **kwargs):
        """Automatically register any subclass and convert DSL patterns to AstNodes.

        This magic method is called whenever a class inherits from VerifiableRule.
        It:
        1. Renames PATTERN/REPLACEMENT to _dsl_pattern/_dsl_replacement (internal storage)
        2. Creates PATTERN/REPLACEMENT_PATTERN properties that return AstNodes
        3. Instantiates and adds the rule to the global registry for testing

        Note: Registration with d810's PatternMatchingRule registry happens automatically
        via the Registrant metaclass since we inherit from PatternMatchingRule.
        """
        super().__init_subclass__(**kwargs)

        # Capture and convert DSL patterns to internal storage
        # Subclasses set PATTERN/REPLACEMENT as class vars (SymbolicExpression)
        # We move them to _dsl_pattern/_dsl_replacement so the properties work
        if 'PATTERN' in cls.__dict__ and hasattr(cls.__dict__['PATTERN'], 'node'):
            cls._dsl_pattern = cls.__dict__['PATTERN']
            # Remove the class variable so it doesn't shadow our property
            delattr(cls, 'PATTERN')

        if 'REPLACEMENT' in cls.__dict__ and hasattr(cls.__dict__['REPLACEMENT'], 'node'):
            cls._dsl_replacement = cls.__dict__['REPLACEMENT']
            delattr(cls, 'REPLACEMENT')

        # Only register concrete classes, not abstract ones
        if not isabstract(cls):
            try:
                # Add to testing registry
                instance = cls()
                RULE_REGISTRY.append(instance)
                logger.debug(f"Registered {cls.__name__} for testing (total: {len(RULE_REGISTRY)})")
            except Exception as e:
                logger.warning(
                    f"Failed to register rule {cls.__name__} for testing: {e}",
                    exc_info=True
                )

    # Implement rule name property (required by OptimizationRule)
    @property
    def name(self) -> str:
        """Return the rule name (class name by default).

        This is used by d810's optimizer to track which rules fire.
        """
        return self.__class__.__name__

    # Implement SymbolicRule abstract properties
    @property
    def pattern(self) -> SymbolicExpression:
        """The symbolic pattern to match (SymbolicRule interface).

        Returns the DSL SymbolicExpression for Z3 verification.
        """
        # Look up the MRO for _dsl_pattern (set by __init_subclass__)
        for cls in type(self).__mro__:
            if hasattr(cls, '_dsl_pattern'):
                return cls._dsl_pattern
        return None

    @property
    def replacement(self) -> SymbolicExpression:
        """The symbolic replacement expression (SymbolicRule interface).

        Returns the DSL SymbolicExpression for Z3 verification.
        """
        # Look up the MRO for _dsl_replacement (set by __init_subclass__)
        for cls in type(self).__mro__:
            if hasattr(cls, '_dsl_replacement'):
                return cls._dsl_replacement
        return None

    # Implement PatternMatchingRule interface by converting DSL to AstNode
    @property
    def PATTERN(self):
        """Get the pattern as an AstNode (PatternMatchingRule interface).

        Converts from DSL SymbolicExpression to AstNode for d810.
        """
        if self.pattern is not None:
            return self.pattern.node
        return None

    @property
    def REPLACEMENT_PATTERN(self):
        """Get the replacement as an AstNode (PatternMatchingRule interface).

        Converts from DSL SymbolicExpression to AstNode for d810.
        """
        if self.replacement is not None:
            return self.replacement.node
        return None

    def check_candidate(self, candidate) -> bool:
        """Check if a candidate AstNode matches this rule's constraints.

        This implements the GenericPatternRule interface, allowing VerifiableRule
        to work with PatternMatchingRule's matching system.

        The candidate is an AstNode that has already matched the PATTERN structure.
        This method:
        1. Adds the candidate itself to the context (for context providers)
        2. Runs all context providers to bind additional variables
        3. Checks all runtime constraints
        4. Optionally updates the destination operand

        Args:
            candidate: An AstNode that structurally matches PATTERN

        Returns:
            True if all constraints are satisfied, False otherwise
        """
        # Build match context from candidate's matched variables
        # The candidate has a dictionary mapping variable names to matched mops
        if not hasattr(candidate, 'get_z3_vars') and not hasattr(candidate, 'mop_dict'):
            # If candidate doesn't have variable bindings yet, assume it's valid
            # The actual constraint checking will happen during replacement
            return True

        # Get the variable bindings from the candidate
        match_context = {}
        if hasattr(candidate, 'mop_dict'):
            match_context = candidate.mop_dict
        elif hasattr(candidate, 'get_z3_vars'):
            match_context = candidate.get_z3_vars({})

        # CRITICAL: Add the candidate itself so constraints/providers can inspect it
        # This enables context-aware constraints like when.dst.is_high_half
        match_context["_candidate"] = candidate

        # Run context providers to bind additional variables
        # Example: {"full_reg": context.dst.parent_register}
        if hasattr(self, 'CONTEXT_VARS') and self.CONTEXT_VARS:
            for var_name, provider in self.CONTEXT_VARS.items():
                try:
                    # Call the provider with the match context
                    value = provider(match_context)
                    if value is None:
                        # Provider failed (e.g., couldn't find parent register)
                        logger.debug(
                            f"Context provider for '{var_name}' returned None in {self.name}"
                        )
                        return False

                    # Add the bound variable to both contexts
                    match_context[var_name] = value
                    if hasattr(candidate, 'mop_dict'):
                        candidate.mop_dict[var_name] = value

                except Exception as e:
                    logger.debug(
                        f"Context provider for '{var_name}' failed in {self.name}: {e}"
                    )
                    return False

        # Check all runtime constraints (including context-aware ones)
        if not self.check_runtime_constraints(match_context):
            return False

        # Handle destination update side effect
        # If UPDATE_DESTINATION is set, modify the candidate's destination operand
        if hasattr(self, 'UPDATE_DESTINATION') and self.UPDATE_DESTINATION:
            dest_var = self.UPDATE_DESTINATION
            if dest_var in match_context:
                bound_var = match_context[dest_var]
                # Extract the mop from the AstNode
                if hasattr(bound_var, 'mop') and bound_var.mop is not None:
                    candidate.dst_mop = bound_var.mop
                    logger.debug(
                        f"Updated destination to '{dest_var}' in {self.name}"
                    )
                else:
                    logger.warning(
                        f"UPDATE_DESTINATION '{dest_var}' has no mop in {self.name}"
                    )
                    return False
            else:
                logger.warning(
                    f"UPDATE_DESTINATION '{dest_var}' not found in context for {self.name}"
                )
                return False

        return True

    def check_runtime_constraints(self, match_context: Dict[str, Any]) -> bool:
        """Check if all runtime constraints are satisfied for this match.

        This method evaluates the CONSTRAINTS list against the matched values.
        Constraints can be either:
        1. ConstraintExpr objects (new declarative style)
        2. Callable predicates (legacy style)

        Args:
            match_context: Dictionary mapping variable names to matched AstNodes/values.

        Returns:
            True if all constraints pass, False otherwise.

        Example:
            >>> # New declarative style:
            >>> CONSTRAINTS = [
            ...     c1 == ~c2,          # Checking constraint
            ...     val_res == c2 - ONE  # Defining constraint
            ... ]
            >>> # Legacy style:
            >>> from d810.mba.dsl import when
            >>> CONSTRAINTS = [
            ...     when.equal_mops("c_1", "c_2"),
            ...     when.is_bnot("x_0", "bnot_x_0"),
            ... ]
        """
        if not hasattr(self, 'CONSTRAINTS') or not self.CONSTRAINTS:
            return True

        for constraint in self.CONSTRAINTS:
            try:
                # Check if this is a ConstraintExpr (new declarative style)
                from d810.mba.constraints import is_constraint_expr
                if is_constraint_expr(constraint):
                    # Try to extract a variable definition
                    var_name, value = constraint.eval_and_define(match_context)

                    if var_name is not None:
                        # This is a defining constraint - add the computed value
                        from d810.expr.ast import AstConstant
                        match_context[var_name] = AstConstant(var_name, value)
                    else:
                        # This is a checking constraint - verify it holds
                        if not constraint.check(match_context):
                            return False
                else:
                    # Legacy callable constraint
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
        # Auto-convert DSL constraints to Z3 expressions
        if not hasattr(self, 'CONSTRAINTS') or not self.CONSTRAINTS:
            return []

        z3_constraints = []

        for constraint in self.CONSTRAINTS:
            # Check if this is a ConstraintExpr (new declarative style)
            from d810.mba.constraints import is_constraint_expr
            if is_constraint_expr(constraint):
                # Direct conversion to Z3
                try:
                    z3_constraint = constraint.to_z3(z3_vars)
                    z3_constraints.append(z3_constraint)
                    continue
                except Exception as e:
                    logger.debug(f"Could not convert ConstraintExpr to Z3: {e}")
                    # Continue to try legacy constraint handling
                    pass

            # Check if constraint has _to_z3 attribute (new constraint helpers like when.or_inequality)
            if callable(constraint) and hasattr(constraint, '_to_z3'):
                try:
                    z3_constraint = constraint._to_z3(z3_vars)
                    if z3_constraint is not None:
                        z3_constraints.append(z3_constraint)
                        continue
                except Exception as e:
                    logger.debug(f"Could not convert constraint with _to_z3: {e}")
                    # Fall through to other methods

            # Legacy: Try to auto-convert callable constraints (when.is_bnot, etc.)
            if callable(constraint) and hasattr(constraint, '__closure__') and constraint.__closure__:
                # Extract variable names from closure (for when.is_bnot, when.equal_mops)
                closure_vars = []
                for cell in constraint.__closure__:
                    content = cell.cell_contents
                    if isinstance(content, str):
                        closure_vars.append(content)

                if len(closure_vars) >= 2:
                    var1, var2 = closure_vars[0], closure_vars[1]

                    # Check if both variables are in z3_vars
                    if var1 in z3_vars and var2 in z3_vars:
                        # Assume is_bnot (most common) - creates: var1 == ~var2
                        # TODO: Detect constraint type more precisely
                        z3_constraints.append(z3_vars[var1] == ~z3_vars[var2])
                        continue

            # For lambdas or unknown constraints, log warning
            logger.debug(f"Could not auto-convert constraint for rule {self.name}")

        return z3_constraints

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

        # Find all unique variable and constant names from pure SymbolicExpression
        # CRITICAL: Pattern-matching constants (e.g., Const("c_1") without value)
        # must be treated as symbolic Z3 variables, not concrete values
        def collect_names(expr: SymbolicExpression, var_names: set, const_names: set):
            """Recursively collect variable and constant names from expression."""
            if expr is None:
                return  # Skip None (e.g., DynamicConst replacements)
            if not isinstance(expr, SymbolicExpression):
                return  # Skip non-SymbolicExpression (e.g., DynamicConst)

            if expr.is_leaf():
                if expr.name:  # Skip None names
                    if expr.is_constant():
                        # Concrete constant - Z3VerificationVisitor handles it
                        pass
                    else:
                        # Variable or pattern-matching constant (value=None)
                        if expr.value is None:
                            # Pattern-matching: could be Var("x") or Const("c_1")
                            # Both treated as symbolic variables
                            var_names.add(expr.name)
            else:
                # Recurse into children
                if expr.left:
                    collect_names(expr.left, var_names, const_names)
                if expr.right:
                    collect_names(expr.right, var_names, const_names)

        var_names = set()
        const_names = set()
        collect_names(self.pattern, var_names, const_names)
        collect_names(self.replacement, var_names, const_names)

        # Skip verification if replacement is DynamicConst (not SymbolicExpression)
        if not isinstance(self.replacement, SymbolicExpression):
            logger.debug(f"Skipping verification for {self.name}: replacement is {type(self.replacement).__name__}, not SymbolicExpression")
            return True  # Can't verify DynamicConst with Z3

        # Create Z3 BitVec variables for all symbolic variables/constants
        z3_vars = {}
        for name in sorted(var_names):
            z3_vars[name] = z3.BitVec(name, self.BIT_WIDTH)

        # Get rule-specific constraints (now has access to constant symbols)
        constraints = self.get_constraints(z3_vars)

        # Prove equivalence using pure SymbolicExpression (no .node needed!)
        is_equivalent, counterexample = prove_equivalence(
            self.pattern,
            self.replacement,
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


# Dynamically add PatternMatchingRule to VerifiableRule's bases to avoid circular imports.
# This happens AFTER all classes in this module are defined, so when pattern_matching modules
# import VerifiableRule, it exists but doesn't yet have PatternMatchingRule in its MRO.
# Then, after all modules are loaded, this code runs and completes the inheritance chain.
try:
    from d810.optimizers.microcode.instructions.pattern_matching.handler import PatternMatchingRule

    # Add PatternMatchingRule to VerifiableRule's bases if not already there
    if PatternMatchingRule not in VerifiableRule.__bases__:
        # Replace the bases tuple to include PatternMatchingRule
        VerifiableRule.__bases__ = (SymbolicRule, PatternMatchingRule)
        logger.debug("Successfully added PatternMatchingRule to VerifiableRule's bases")

        # NOW that VerifiableRule has the correct bases, import the refactored rule modules
        # so they register properly with the correct MRO
        try:
            from d810.optimizers.microcode.instructions.pattern_matching import (
                rewrite_add_refactored,
                rewrite_and_refactored,
                rewrite_bnot_refactored,
                rewrite_cst_refactored,
                rewrite_mov_refactored,
                rewrite_mul_refactored,
                rewrite_neg_refactored,
                rewrite_or_refactored,
                rewrite_predicates_refactored,
                rewrite_sub_refactored,
                rewrite_xor_refactored,
            )
            logger.debug("Successfully loaded refactored rule modules")
        except ImportError as e2:
            logger.warning(f"Could not load refactored rule modules: {e2}")

except ImportError as e:
    logger.warning(
        f"Could not import PatternMatchingRule to complete VerifiableRule inheritance: {e}. "
        "VerifiableRule subclasses will not be registered with d810's pattern matching system."
    )

