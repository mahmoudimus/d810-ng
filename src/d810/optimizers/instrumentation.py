"""Instrumentation and tracking for deobfuscation analysis.

This module provides comprehensive tracking of optimization activity
for testing, profiling, and analysis. It captures:

- Which rules fired and how many times
- What changes each rule made
- CFG structural changes (blocks, edges, patches)
- Flow optimization details (unflattening, loop unwrapping, etc.)
- Pattern matching statistics

This instrumentation is used by tests to make structural assertions
about deobfuscation quality.
"""

from __future__ import annotations

import dataclasses
import logging
from collections import defaultdict
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Set

from d810.conf.loggers import getLogger

logger = getLogger("D810.instrumentation")


@dataclass
class CFGStatistics:
    """Control Flow Graph structural statistics.

    Tracks changes to the CFG structure during optimization:
    - Blocks added/removed
    - Edges redirected
    - Switch cases flattened/unflattened
    """

    # Block counts
    blocks_initial: int = 0
    blocks_final: int = 0
    blocks_added: int = 0
    blocks_removed: int = 0
    blocks_duplicated: int = 0

    # Edge statistics
    edges_redirected: int = 0
    edges_added: int = 0
    edges_removed: int = 0

    # Control flow structures
    switch_cases_initial: int = 0
    switch_cases_final: int = 0
    loops_found: int = 0
    dispatchers_found: int = 0

    def blocks_delta(self) -> int:
        """Net change in block count."""
        return self.blocks_final - self.blocks_initial

    def switch_cases_delta(self) -> int:
        """Net change in switch cases."""
        return self.switch_cases_final - self.switch_cases_initial

    def get_summary(self) -> Dict[str, Any]:
        """Get statistics summary as a dict."""
        return {
            "blocks": {
                "initial": self.blocks_initial,
                "final": self.blocks_final,
                "delta": self.blocks_delta(),
                "added": self.blocks_added,
                "removed": self.blocks_removed,
                "duplicated": self.blocks_duplicated,
            },
            "edges": {
                "redirected": self.edges_redirected,
                "added": self.edges_added,
                "removed": self.edges_removed,
            },
            "control_flow": {
                "switch_cases_initial": self.switch_cases_initial,
                "switch_cases_final": self.switch_cases_final,
                "switch_cases_delta": self.switch_cases_delta(),
                "loops_found": self.loops_found,
                "dispatchers_found": self.dispatchers_found,
            }
        }


@dataclass
class RuleExecution:
    """Details about a single rule execution."""
    rule_name: str
    rule_type: str  # "flow", "instruction", "pattern"
    changes_made: int
    execution_order: int  # Sequence number for this execution
    maturity: int
    metadata: Dict[str, Any] = field(default_factory=dict)  # Rule-specific data

    def __str__(self) -> str:
        return f"{self.rule_name}({self.rule_type}): {self.changes_made} changes at maturity {self.maturity}"


@dataclass
class FlowRuleExecution(RuleExecution):
    """Extended execution info for flow optimization rules."""

    # Unflattening-specific
    dispatchers_processed: int = 0
    edges_unflattened: int = 0
    goto_tables_found: int = 0

    # Loop-specific
    loops_unwrapped: int = 0
    loop_iterations_found: int = 0

    # Block-specific
    blocks_duplicated: int = 0
    blocks_merged: int = 0

    def get_details(self) -> Dict[str, Any]:
        """Get flow-specific details."""
        return {
            "unflattening": {
                "dispatchers_processed": self.dispatchers_processed,
                "edges_unflattened": self.edges_unflattened,
                "goto_tables_found": self.goto_tables_found,
            },
            "loops": {
                "loops_unwrapped": self.loops_unwrapped,
                "iterations_found": self.loop_iterations_found,
            },
            "blocks": {
                "duplicated": self.blocks_duplicated,
                "merged": self.blocks_merged,
            }
        }


@dataclass
class PatternRuleExecution(RuleExecution):
    """Extended execution info for pattern matching rules."""

    # Pattern details
    patterns_matched: int = 0
    patterns_replaced: int = 0

    # Specific pattern types
    xor_patterns: int = 0
    and_patterns: int = 0
    or_patterns: int = 0
    neg_patterns: int = 0
    mba_patterns: int = 0
    constant_folds: int = 0

    def get_details(self) -> Dict[str, Any]:
        """Get pattern-specific details."""
        return {
            "patterns": {
                "matched": self.patterns_matched,
                "replaced": self.patterns_replaced,
            },
            "by_type": {
                "xor": self.xor_patterns,
                "and": self.and_patterns,
                "or": self.or_patterns,
                "neg": self.neg_patterns,
                "mba": self.mba_patterns,
                "constant_folds": self.constant_folds,
            }
        }


@dataclass
class DeobfuscationContext:
    """Comprehensive tracking of all deobfuscation activity.

    This context captures everything that happens during optimization:
    - Which rules fired in which order
    - What changes each rule made
    - CFG structural transformations
    - Pattern matching statistics

    Test assertions can use this to verify:
    - "Unflattener rule fired exactly once"
    - "Redirected 15 edges during unflattening"
    - "XOR pattern matched 23 times"
    - "Reduced switch cases from 18 to 3"

    Example:
        >>> ctx = DeobfuscationContext()
        >>> ctx.record_rule_execution("UnflattenerRule", "flow", 15, maturity=2,
        ...                           metadata={"dispatchers": 1, "edges": 15})
        >>> assert ctx.rule_fired("UnflattenerRule")
        >>> assert ctx.rule_fire_count("UnflattenerRule") == 1
        >>> assert ctx.total_changes_by_rule("UnflattenerRule") == 15
    """

    # Rule execution history (in order)
    executions: List[RuleExecution] = field(default_factory=list)

    # CFG structural statistics
    cfg_stats: CFGStatistics = field(default_factory=CFGStatistics)

    # Aggregated statistics
    rules_fired: Dict[str, int] = field(default_factory=lambda: defaultdict(int))
    changes_by_rule: Dict[str, int] = field(default_factory=lambda: defaultdict(int))
    rules_by_type: Dict[str, List[str]] = field(default_factory=lambda: defaultdict(list))

    # Maturity tracking
    maturities_processed: Set[int] = field(default_factory=set)
    total_passes: int = 0

    # Metadata
    function_name: Optional[str] = None
    function_address: Optional[int] = None

    def record_rule_execution(
        self,
        rule_name: str,
        rule_type: str,
        changes: int,
        maturity: int,
        metadata: Optional[Dict[str, Any]] = None
    ) -> RuleExecution:
        """Record that a rule was executed.

        Args:
            rule_name: Name of the rule (e.g., "UnflattenerTigress")
            rule_type: Type of rule ("flow", "instruction", "pattern")
            changes: Number of changes the rule made
            maturity: Maturity level when executed
            metadata: Optional rule-specific metadata

        Returns:
            The created RuleExecution record
        """
        execution_order = len(self.executions)

        # Create appropriate execution record
        if rule_type == "flow":
            execution = FlowRuleExecution(
                rule_name=rule_name,
                rule_type=rule_type,
                changes_made=changes,
                execution_order=execution_order,
                maturity=maturity,
                metadata=metadata or {}
            )
        elif rule_type == "pattern":
            execution = PatternRuleExecution(
                rule_name=rule_name,
                rule_type=rule_type,
                changes_made=changes,
                execution_order=execution_order,
                maturity=maturity,
                metadata=metadata or {}
            )
        else:
            execution = RuleExecution(
                rule_name=rule_name,
                rule_type=rule_type,
                changes_made=changes,
                execution_order=execution_order,
                maturity=maturity,
                metadata=metadata or {}
            )

        # Record execution
        self.executions.append(execution)
        self.rules_fired[rule_name] += 1
        self.changes_by_rule[rule_name] += changes
        self.rules_by_type[rule_type].append(rule_name)
        self.maturities_processed.add(maturity)

        logger.debug(f"Recorded execution: {execution}")
        return execution

    def record_flow_rule_execution(
        self,
        rule_name: str,
        changes: int,
        maturity: int,
        dispatchers: int = 0,
        edges_unflattened: int = 0,
        loops_unwrapped: int = 0,
        **kwargs
    ) -> FlowRuleExecution:
        """Convenience method for recording flow rule execution."""
        metadata = {
            "dispatchers": dispatchers,
            "edges_unflattened": edges_unflattened,
            "loops_unwrapped": loops_unwrapped,
            **kwargs
        }

        exec_record = self.record_rule_execution(
            rule_name=rule_name,
            rule_type="flow",
            changes=changes,
            maturity=maturity,
            metadata=metadata
        )

        # Update flow-specific fields if it's a FlowRuleExecution
        if isinstance(exec_record, FlowRuleExecution):
            exec_record.dispatchers_processed = dispatchers
            exec_record.edges_unflattened = edges_unflattened
            exec_record.loops_unwrapped = loops_unwrapped

        # Update CFG stats
        self.cfg_stats.edges_redirected += edges_unflattened
        self.cfg_stats.dispatchers_found += dispatchers

        return exec_record

    def record_pattern_rule_execution(
        self,
        rule_name: str,
        changes: int,
        maturity: int,
        patterns_matched: int = 0,
        pattern_type: Optional[str] = None,
        **kwargs
    ) -> PatternRuleExecution:
        """Convenience method for recording pattern rule execution."""
        metadata = {
            "patterns_matched": patterns_matched,
            "pattern_type": pattern_type,
            **kwargs
        }

        exec_record = self.record_rule_execution(
            rule_name=rule_name,
            rule_type="pattern",
            changes=changes,
            maturity=maturity,
            metadata=metadata
        )

        # Update pattern-specific fields
        if isinstance(exec_record, PatternRuleExecution):
            exec_record.patterns_matched = patterns_matched
            exec_record.patterns_replaced = changes

            # Track by pattern type
            if pattern_type:
                if "xor" in pattern_type.lower():
                    exec_record.xor_patterns += changes
                elif "and" in pattern_type.lower():
                    exec_record.and_patterns += changes
                elif "or" in pattern_type.lower():
                    exec_record.or_patterns += changes
                elif "neg" in pattern_type.lower():
                    exec_record.neg_patterns += changes
                elif "mba" in pattern_type.lower() or "guessing" in pattern_type.lower():
                    exec_record.mba_patterns += changes
                elif "cst" in pattern_type.lower() or "constant" in pattern_type.lower():
                    exec_record.constant_folds += changes

        return exec_record

    def record_cfg_changes(
        self,
        blocks_added: int = 0,
        blocks_removed: int = 0,
        edges_redirected: int = 0,
        switch_cases_removed: int = 0
    ):
        """Record CFG structural changes."""
        self.cfg_stats.blocks_added += blocks_added
        self.cfg_stats.blocks_removed += blocks_removed
        self.cfg_stats.edges_redirected += edges_redirected
        self.cfg_stats.switch_cases_final -= switch_cases_removed

    # Query methods for test assertions

    def rule_fired(self, rule_name: str) -> bool:
        """Check if a specific rule fired."""
        return rule_name in self.rules_fired

    def rule_fire_count(self, rule_name: str) -> int:
        """Get how many times a rule fired."""
        return self.rules_fired.get(rule_name, 0)

    def total_changes_by_rule(self, rule_name: str) -> int:
        """Get total changes made by a specific rule."""
        return self.changes_by_rule.get(rule_name, 0)

    def total_changes(self) -> int:
        """Get total changes across all rules."""
        return sum(self.changes_by_rule.values())

    def flow_rules_that_fired(self) -> List[str]:
        """Get list of flow rules that fired."""
        return [name for name in self.rules_by_type["flow"] if self.rules_fired[name] > 0]

    def pattern_rules_that_fired(self) -> List[str]:
        """Get list of pattern rules that fired."""
        return [name for name in self.rules_by_type["pattern"] if self.rules_fired[name] > 0]

    def unflattening_occurred(self) -> bool:
        """Check if any unflattening happened."""
        return any("unflatten" in name.lower() for name in self.flow_rules_that_fired())

    def edges_unflattened(self) -> int:
        """Get total edges that were unflattened."""
        total = 0
        for exec in self.executions:
            if isinstance(exec, FlowRuleExecution):
                total += exec.edges_unflattened
        return total

    def pattern_matches_by_type(self, pattern_type: str) -> int:
        """Get number of pattern matches for a specific type (xor, and, mba, etc.)."""
        total = 0
        for exec in self.executions:
            if isinstance(exec, PatternRuleExecution):
                if pattern_type.lower() == "xor":
                    total += exec.xor_patterns
                elif pattern_type.lower() == "and":
                    total += exec.and_patterns
                elif pattern_type.lower() == "or":
                    total += exec.or_patterns
                elif pattern_type.lower() == "neg":
                    total += exec.neg_patterns
                elif pattern_type.lower() == "mba":
                    total += exec.mba_patterns
                elif pattern_type.lower() == "constant":
                    total += exec.constant_folds
        return total

    def get_summary(self) -> Dict[str, Any]:
        """Get a comprehensive summary of deobfuscation activity."""
        return {
            "function": {
                "name": self.function_name,
                "address": hex(self.function_address) if self.function_address else None,
            },
            "execution": {
                "total_passes": self.total_passes,
                "total_rules_fired": len(self.rules_fired),
                "total_changes": self.total_changes(),
                "maturities_processed": sorted(self.maturities_processed),
            },
            "rules": {
                "flow_rules": len(self.flow_rules_that_fired()),
                "pattern_rules": len(self.pattern_rules_that_fired()),
                "by_rule": {
                    name: {
                        "fire_count": self.rule_fire_count(name),
                        "total_changes": self.total_changes_by_rule(name),
                    }
                    for name in sorted(self.rules_fired.keys())
                },
            },
            "cfg": self.cfg_stats.get_summary(),
            "patterns": {
                "xor": self.pattern_matches_by_type("xor"),
                "and": self.pattern_matches_by_type("and"),
                "or": self.pattern_matches_by_type("or"),
                "neg": self.pattern_matches_by_type("neg"),
                "mba": self.pattern_matches_by_type("mba"),
                "constant": self.pattern_matches_by_type("constant"),
            },
        }

    def print_summary(self):
        """Print a human-readable summary to the logger."""
        summary = self.get_summary()

        logger.info("=" * 80)
        logger.info("DEOBFUSCATION CONTEXT SUMMARY")
        logger.info("=" * 80)

        if self.function_name:
            logger.info(f"Function: {self.function_name} @ {summary['function']['address']}")

        logger.info(f"\nExecution:")
        logger.info(f"  Total passes: {summary['execution']['total_passes']}")
        logger.info(f"  Rules fired: {summary['execution']['total_rules_fired']}")
        logger.info(f"  Total changes: {summary['execution']['total_changes']}")
        logger.info(f"  Maturities: {summary['execution']['maturities_processed']}")

        logger.info(f"\nRules:")
        logger.info(f"  Flow rules: {summary['rules']['flow_rules']}")
        logger.info(f"  Pattern rules: {summary['rules']['pattern_rules']}")

        logger.info(f"\nTop 10 rules by changes:")
        sorted_rules = sorted(
            summary['rules']['by_rule'].items(),
            key=lambda x: x[1]['total_changes'],
            reverse=True
        )[:10]
        for rule_name, stats in sorted_rules:
            logger.info(f"  {rule_name}: {stats['total_changes']} changes ({stats['fire_count']}x)")

        logger.info(f"\nCFG Statistics:")
        cfg = summary['cfg']
        logger.info(f"  Blocks: {cfg['blocks']['initial']} → {cfg['blocks']['final']} (Δ{cfg['blocks']['delta']})")
        logger.info(f"  Edges redirected: {cfg['edges']['redirected']}")
        logger.info(f"  Dispatchers found: {cfg['control_flow']['dispatchers_found']}")
        logger.info(f"  Switch cases: {cfg['control_flow']['switch_cases_initial']} → {cfg['control_flow']['switch_cases_final']}")

        logger.info(f"\nPattern Matches:")
        patterns = summary['patterns']
        logger.info(f"  XOR patterns: {patterns['xor']}")
        logger.info(f"  AND patterns: {patterns['and']}")
        logger.info(f"  OR patterns: {patterns['or']}")
        logger.info(f"  NEG patterns: {patterns['neg']}")
        logger.info(f"  MBA patterns: {patterns['mba']}")
        logger.info(f"  Constant folds: {patterns['constant']}")

        logger.info("=" * 80)

    def reset(self):
        """Reset all tracking data."""
        self.executions.clear()
        self.cfg_stats = CFGStatistics()
        self.rules_fired.clear()
        self.changes_by_rule.clear()
        self.rules_by_type.clear()
        self.maturities_processed.clear()
        self.total_passes = 0
        self.function_name = None
        self.function_address = None


# Global context accessor (for use by optimizer hooks)
_current_deobfuscation_context: Optional[DeobfuscationContext] = None


def get_current_deobfuscation_context() -> Optional[DeobfuscationContext]:
    """Get the current deobfuscation context (if any).

    This is used by optimizer hooks to record rule executions.
    Returns None if no context is active.
    """
    return _current_deobfuscation_context


def set_current_deobfuscation_context(ctx: Optional[DeobfuscationContext]):
    """Set the current deobfuscation context (used by test infrastructure)."""
    global _current_deobfuscation_context
    _current_deobfuscation_context = ctx
