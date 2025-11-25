"""IDA Pro backend for MBA expressions and rule pattern matching.

This module provides:

1. IDAPatternAdapter - Wraps a VerifiableRule for use with IDA pattern matching
2. IDANodeVisitor - Converts SymbolicExpression → AstNode for IDA

All IDA-dependent code for rule execution should be in this module, keeping
the rule definitions in d810.mba.rules pure and backend-agnostic.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Any, Dict, List, Optional

from d810.core import getLogger

logger = getLogger(__name__)

# Type hints only - avoid importing IDA at module level
if TYPE_CHECKING:
    from d810.mba.dsl import SymbolicExpression
    from d810.mba.rules import VerifiableRule
    from d810.expr.ast import AstNode, AstLeaf


class IDANodeVisitor:
    """Converts SymbolicExpression trees to IDA AstNode trees.

    This visitor handles the conversion from the pure DSL representation
    to IDA's internal AST format for pattern matching.

    Example:
        >>> from d810.mba.dsl import Var
        >>> x, y = Var("x"), Var("y")
        >>> pattern = (x | y) - (x & y)
        >>> visitor = IDANodeVisitor()
        >>> ast_node = visitor.visit(pattern)
    """

    def visit(self, expr: SymbolicExpression) -> AstNode:
        """Convert a SymbolicExpression to an AstNode.

        Args:
            expr: The SymbolicExpression to convert.

        Returns:
            An AstNode representing the same expression.
        """
        # Import IDA-dependent modules lazily
        from d810.expr.ast import AstNode, AstLeaf, AstConstant

        if expr is None:
            return None

        if expr.is_leaf():
            return self._visit_leaf(expr)

        # Convert children recursively
        left = self.visit(expr.left) if expr.left else None
        right = self.visit(expr.right) if expr.right else None

        # Create AstNode with the opcode
        return AstNode(expr.opcode, left, right)

    def _visit_leaf(self, expr: SymbolicExpression) -> AstLeaf:
        """Convert a leaf SymbolicExpression to an AstLeaf.

        Args:
            expr: The leaf SymbolicExpression to convert.

        Returns:
            An AstLeaf or AstConstant representing the leaf.
        """
        from d810.expr.ast import AstLeaf, AstConstant

        if expr.is_constant():
            # Concrete constant (has a value)
            return AstConstant(expr.name, expr.value)
        else:
            # Variable or pattern-matching placeholder
            return AstLeaf(expr.name)


class IDAPatternAdapter:
    """Adapts a VerifiableRule for use with IDA pattern matching.

    This adapter wraps a pure VerifiableRule and provides the IDA-specific
    interface required by PatternOptimizer:
    - pattern_candidates property
    - get_valid_candidates() method
    - get_replacement() method
    - check_and_replace() method

    The rule itself remains pure (no IDA dependencies). All IDA-specific
    logic is encapsulated in this adapter.

    Example:
        >>> from d810.mba.rules import VerifiableRule
        >>> from d810.mba.backends.ida import IDAPatternAdapter
        >>>
        >>> # Create adapter from rule
        >>> adapter = IDAPatternAdapter(my_rule)
        >>>
        >>> # Use in IDA context
        >>> new_ins = adapter.check_and_replace(blk, instruction)
    """

    def __init__(self, rule: VerifiableRule):
        """Initialize the adapter with a rule.

        Args:
            rule: The VerifiableRule to adapt for IDA.
        """
        self.rule = rule
        self._pattern_candidates_cache: Optional[List[AstNode]] = None
        self._visitor = IDANodeVisitor()

    # ==========================================================================
    # Properties delegated to the underlying rule
    # ==========================================================================

    @property
    def name(self) -> str:
        """Return the rule name."""
        return self.rule.name

    @property
    def description(self) -> str:
        """Return the rule description."""
        return self.rule.description

    @property
    def maturities(self) -> list:
        """Return the maturities this rule applies to."""
        return getattr(self.rule, 'maturities', [])

    @property
    def config(self) -> dict:
        """Return the rule configuration."""
        return getattr(self.rule, 'config', {})

    # ==========================================================================
    # IDA Pattern Matching Interface
    # ==========================================================================

    @property
    def pattern_candidates(self) -> List[AstNode]:
        """Get pattern candidates as AstNodes (lazy conversion from DSL).

        This property lazily converts the DSL SymbolicExpression to AstNode
        only when accessed in IDA context.
        """
        if self._pattern_candidates_cache is None:
            pattern = self.rule.pattern
            if pattern is not None:
                ast_node = self._visitor.visit(pattern)
                self._pattern_candidates_cache = [ast_node] if ast_node else []
            else:
                self._pattern_candidates_cache = []
        return self._pattern_candidates_cache

    @property
    def PATTERN(self) -> Optional[AstNode]:
        """Get the pattern as an AstNode (PatternMatchingRule interface)."""
        pattern = self.rule.pattern
        if pattern is not None:
            return self._visitor.visit(pattern)
        return None

    @property
    def REPLACEMENT_PATTERN(self) -> Optional[AstNode]:
        """Get the replacement as an AstNode (PatternMatchingRule interface)."""
        replacement = self.rule.replacement
        if replacement is not None:
            return self._visitor.visit(replacement)
        return None

    def get_valid_candidates(self, instruction, stop_early: bool = True) -> list:
        """Match the instruction against this rule's patterns.

        Args:
            instruction: The IDA minsn_t instruction to match.
            stop_early: If True, return after first match.

        Returns:
            List of matched candidate AstNodes.
        """
        from d810.expr.ast import minsn_to_ast

        valid_candidates = []
        tmp = minsn_to_ast(instruction)
        if tmp is None:
            return []

        for candidate_pattern in self.pattern_candidates:
            if not candidate_pattern:
                continue
            # Use a read-only check first
            if not candidate_pattern.check_pattern_and_copy_mops(tmp, read_only=True):
                continue
            if not self._check_candidate(candidate_pattern):
                continue
            # If the read-only check passes, create a mutable copy
            mutable_candidate = candidate_pattern.clone()
            if not mutable_candidate.check_pattern_and_copy_mops(tmp):
                continue
            valid_candidates.append(mutable_candidate)
            if stop_early:
                return valid_candidates
        return []

    def get_replacement(self, candidate) -> Optional[Any]:
        """Create a replacement instruction from a matched candidate.

        Args:
            candidate: The matched AstNode candidate.

        Returns:
            A new minsn_t instruction, or None if replacement failed.
        """
        repl_pat = self.REPLACEMENT_PATTERN
        if not repl_pat:
            logger.debug(f"No replacement pattern for rule {self.name}")
            return None

        is_ok = repl_pat.update_leafs_mop(candidate)
        if not is_ok:
            logger.debug(f"Failed to update leaf mops for rule {self.name}")
            return None

        if not candidate.ea:
            logger.debug(f"No EA for candidate in rule {self.name}")
            return None

        new_ins = repl_pat.create_minsn(candidate.ea, candidate.dst_mop)
        return new_ins

    def check_and_replace(self, blk, instruction) -> Optional[Any]:
        """Check if this rule matches and return a replacement instruction.

        This is the main entry point called by the optimizer system.

        Args:
            blk: The microcode block (mblock_t).
            instruction: The instruction to check (minsn_t).

        Returns:
            A new minsn_t if the rule matched, None otherwise.
        """
        valid_candidates = self.get_valid_candidates(instruction, stop_early=True)
        if len(valid_candidates) == 0:
            return None
        new_instruction = self.get_replacement(valid_candidates[0])
        return new_instruction

    def check_pattern_and_replace(self, candidate_pattern, test_ast) -> Optional[Any]:
        """Check if this rule matches a pattern and return a replacement.

        This method is used by PatternOptimizer's pattern storage lookup system.

        Args:
            candidate_pattern: A candidate AstNode pattern from the pattern storage.
            test_ast: The AstNode converted from the microcode instruction.

        Returns:
            A new minsn_t if the rule matched, None otherwise.
        """
        # First, check if the pattern matches the test AST
        if not candidate_pattern.check_pattern_and_copy_mops(test_ast):
            return None

        # Then check candidate-level constraints
        if not self._check_candidate(candidate_pattern):
            return None

        # Finally, create the replacement instruction
        new_instruction = self.get_replacement(candidate_pattern)
        return new_instruction

    # ==========================================================================
    # Internal constraint checking (delegates to rule)
    # ==========================================================================

    def _check_candidate(self, candidate) -> bool:
        """Check if a candidate AstNode matches this rule's constraints.

        Delegates to the underlying rule's check_candidate method if available,
        otherwise performs basic constraint checking.

        Args:
            candidate: An AstNode that structurally matches PATTERN

        Returns:
            True if all constraints are satisfied, False otherwise
        """
        # If rule has check_candidate, use it
        if hasattr(self.rule, 'check_candidate'):
            return self.rule.check_candidate(candidate)

        # Fallback: check runtime constraints directly
        return self._check_runtime_constraints(candidate)

    def _check_runtime_constraints(self, candidate) -> bool:
        """Check runtime constraints against a matched candidate.

        Args:
            candidate: The matched AstNode with variable bindings.

        Returns:
            True if all constraints pass, False otherwise.
        """
        constraints = getattr(self.rule, 'CONSTRAINTS', [])
        if not constraints:
            return True

        # Build match context from candidate's matched variables
        match_context = {}
        if hasattr(candidate, 'mop_dict'):
            match_context = candidate.mop_dict
        elif hasattr(candidate, 'get_z3_vars'):
            match_context = candidate.get_z3_vars({})

        # Add candidate itself to context
        match_context["_candidate"] = candidate

        # Check each constraint
        for constraint in constraints:
            try:
                # Check if this is a ConstraintExpr
                from d810.mba.constraints import is_constraint_expr
                if is_constraint_expr(constraint):
                    if not constraint.check(match_context):
                        return False
                elif callable(constraint):
                    if not constraint(match_context):
                        return False
            except Exception as e:
                logger.debug(f"Constraint check failed for {self.name}: {e}")
                return False

        return True

    # ==========================================================================
    # Configuration interface (required by d810 optimizer system)
    # ==========================================================================

    def configure(self, kwargs: Dict[str, Any]) -> None:
        """Configure this rule with options from a JSON config.

        Args:
            kwargs: Configuration dictionary from the JSON project file.
        """
        if hasattr(self.rule, 'configure'):
            self.rule.configure(kwargs)

    def set_log_dir(self, log_dir: str) -> None:
        """Set the log directory for this rule.

        Args:
            log_dir: Path to the log directory.
        """
        if hasattr(self.rule, 'set_log_dir'):
            self.rule.set_log_dir(log_dir)


def adapt_rules(rules: List[VerifiableRule]) -> List[IDAPatternAdapter]:
    """Wrap a list of rules with IDAPatternAdapter for IDA integration.

    Args:
        rules: List of VerifiableRule instances.

    Returns:
        List of IDAPatternAdapter instances wrapping the rules.

    Example:
        >>> from d810.mba.rules import VerifiableRule
        >>> from d810.mba.backends.ida import adapt_rules
        >>>
        >>> rule_instances = VerifiableRule.instantiate_all()
        >>> ida_rules = adapt_rules(rule_instances)
    """
    return [IDAPatternAdapter(rule) for rule in rules]


__all__ = [
    'IDANodeVisitor',
    'IDAPatternAdapter',
    'adapt_rules',
]
