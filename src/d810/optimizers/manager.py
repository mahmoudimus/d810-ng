"""Centralized optimizer manager for coordinating all optimization rules.

This module implements Phase 3 of the refactoring plan: centralizing the
optimization loop in a single, well-defined manager class instead of having
each rule manage its own execution.

The OptimizerManager:
- Loads and instantiates all optimization rules
- Creates immutable OptimizationContext for each pass
- Coordinates rule execution at appropriate maturities
- Tracks usage statistics
- Provides clear hooks for profiling and caching

This replaces the scattered logic where individual rules check maturity,
manage their own state, and decide when to run.
"""

from __future__ import annotations

import logging
from collections import defaultdict
from dataclasses import dataclass, field
from typing import Any, Dict, List, Type

from ida_hexrays import mba_t, mblock_t, minsn_t

from d810.conf.loggers import getLogger
from d810.optimizers.core import OptimizationContext, OptimizationRule

logger = getLogger("D810.manager")


@dataclass
class RuleRegistry:
    """Registry for organizing optimization rules by type and maturity.

    Rules are categorized into:
    - Flow rules: Operate on control flow graph (blocks)
    - Instruction rules: Operate on individual instructions
    - Pattern rules: Match and replace AST patterns

    Each rule specifies which maturities it should run at.
    """
    flow_rules: List[OptimizationRule] = field(default_factory=list)
    instruction_rules: List[OptimizationRule] = field(default_factory=list)
    pattern_rules: List[OptimizationRule] = field(default_factory=list)

    def all_rules(self) -> List[OptimizationRule]:
        """Get all registered rules."""
        return self.flow_rules + self.instruction_rules + self.pattern_rules

    def count(self) -> int:
        """Get total number of registered rules."""
        return len(self.flow_rules) + len(self.instruction_rules) + len(self.pattern_rules)


@dataclass
class OptimizationStatistics:
    """Statistics for tracking rule usage and performance.

    This allows profiling which rules are most effective and where
    time is being spent.
    """
    rules_applied: Dict[str, int] = field(default_factory=lambda: defaultdict(int))
    changes_made: Dict[str, int] = field(default_factory=lambda: defaultdict(int))
    total_passes: int = 0

    def record_application(self, rule_name: str, changes: int) -> None:
        """Record that a rule was applied with the given number of changes."""
        self.rules_applied[rule_name] += 1
        if changes > 0:
            self.changes_made[rule_name] += changes

    def get_summary(self) -> str:
        """Get a human-readable summary of statistics."""
        lines = [
            f"Total passes: {self.total_passes}",
            f"Rules with changes: {len([r for r in self.changes_made if self.changes_made[r] > 0])}",
            "",
            "Top 10 rules by changes:"
        ]

        sorted_rules = sorted(
            self.changes_made.items(),
            key=lambda x: x[1],
            reverse=True
        )[:10]

        for rule_name, changes in sorted_rules:
            applications = self.rules_applied[rule_name]
            lines.append(f"  {rule_name}: {changes} changes in {applications} applications")

        return "\n".join(lines)


class OptimizerManager:
    """Centralized manager for all microcode optimization rules.

    This class replaces the scattered optimization logic with a single,
    coordinated approach. Instead of each rule managing its own lifecycle,
    the manager:

    1. Loads all rules once at startup
    2. Creates immutable context for each pass
    3. Applies rules in the correct order
    4. Tracks statistics
    5. Provides hooks for caching and profiling

    Example:
        >>> config = {"enable_z3_rules": True}
        >>> manager = OptimizerManager(config, log_dir="/tmp/d810")
        >>>
        >>> # Register rules
        >>> manager.register_flow_rule(UnflattenerRule(...))
        >>> manager.register_pattern_rule(XorFromOrAndSub())
        >>>
        >>> # Apply optimizations
        >>> changes = manager.optimize(mba, maturity=MMAT_GLBOPT1)
        >>> print(manager.get_statistics())

    Architecture:
        This manager follows the Coordinator pattern - it doesn't do the
        optimization itself, but orchestrates the rules that do.

        OLD (scattered):
            Each rule checks maturity → modifies self.mba → tracks its own stats

        NEW (centralized):
            Manager checks maturity → creates context → passes to rules → collects stats
    """

    def __init__(self, config: Dict[str, Any], log_dir: str = "/tmp/d810"):
        """Initialize the optimizer manager.

        Args:
            config: Configuration dictionary for optimization behavior.
            log_dir: Directory for debug logs and intermediate microcode dumps.
        """
        self.config = config
        self.log_dir = log_dir
        self.registry = RuleRegistry()
        self.statistics = OptimizationStatistics()

        # Hook points for extensions
        self.pre_pass_hook = None
        self.post_pass_hook = None
        self.cache_loader = None
        self.cache_saver = None

        logger.info("OptimizerManager initialized with config: %s", config)

    def register_flow_rule(self, rule: OptimizationRule) -> None:
        """Register a flow optimization rule (operates on blocks)."""
        self.registry.flow_rules.append(rule)
        logger.debug("Registered flow rule: %s", rule.name)

    def register_instruction_rule(self, rule: OptimizationRule) -> None:
        """Register an instruction optimization rule (operates on instructions)."""
        self.registry.instruction_rules.append(rule)
        logger.debug("Registered instruction rule: %s", rule.name)

    def register_pattern_rule(self, rule: OptimizationRule) -> None:
        """Register a pattern matching rule (AST-based)."""
        self.registry.pattern_rules.append(rule)
        logger.debug("Registered pattern rule: %s", rule.name)

    def load_rules_from_module(self, module_path: str) -> int:
        """Dynamically load rules from a Python module.

        This allows rules to be defined in separate files and loaded
        at runtime based on configuration.

        Args:
            module_path: Python module path (e.g., "d810.optimizers.microcode.instructions")

        Returns:
            Number of rules loaded.
        """
        # TODO: Implement dynamic loading
        # This would use importlib to load modules and find OptimizationRule subclasses
        logger.warning("Dynamic rule loading not yet implemented")
        return 0

    def optimize(self, mba: mba_t, maturity: int) -> int:
        """Apply all appropriate optimization rules at the given maturity.

        This is the main entry point. It:
        1. Creates an immutable context
        2. Applies flow rules to blocks
        3. Applies instruction rules to instructions
        4. Applies pattern rules to instructions
        5. Returns total changes

        Args:
            mba: The microcode array to optimize.
            maturity: The current maturity level.

        Returns:
            Total number of changes made.
        """
        # Check cache first (if enabled)
        if self.cache_loader:
            cached_result = self.cache_loader(mba, maturity)
            if cached_result is not None:
                logger.info("Loaded optimizations from cache")
                return cached_result

        # Create immutable context
        context = OptimizationContext(
            mba=mba,
            maturity=maturity,
            config=self.config,
            logger=logger,
            log_dir=self.log_dir
        )

        # Pre-pass hook (for profiling, logging, etc.)
        if self.pre_pass_hook:
            self.pre_pass_hook(context)

        total_changes = 0
        self.statistics.total_passes += 1

        # Apply flow rules to the entry block
        # (Flow rules typically process the entire CFG from the entry)
        if self.registry.flow_rules:
            entry_block = mba.get_mblock(0)
            for rule in self.registry.flow_rules:
                try:
                    changes = rule.apply(context, entry_block)
                    total_changes += changes
                    self.statistics.record_application(rule.name, changes)

                    if changes > 0:
                        logger.info(f"{rule.name}: {changes} changes")
                except Exception as e:
                    logger.error(
                        f"Error applying flow rule {rule.name}: {e}",
                        exc_info=True
                    )

        # Apply instruction and pattern rules to all blocks
        if self.registry.instruction_rules or self.registry.pattern_rules:
            for block_idx in range(mba.qty):
                block = mba.get_mblock(block_idx)
                if block is None:
                    continue

                # Apply instruction rules
                for rule in self.registry.instruction_rules:
                    ins = block.head
                    while ins is not None:
                        try:
                            changes = rule.apply(context, ins)
                            total_changes += changes
                            self.statistics.record_application(rule.name, changes)
                        except Exception as e:
                            logger.error(
                                f"Error applying instruction rule {rule.name}: {e}",
                                exc_info=True
                            )
                        ins = ins.next

                # Apply pattern rules (typically also instruction-level)
                for rule in self.registry.pattern_rules:
                    ins = block.head
                    while ins is not None:
                        try:
                            changes = rule.apply(context, ins)
                            total_changes += changes
                            self.statistics.record_application(rule.name, changes)
                        except Exception as e:
                            logger.error(
                                f"Error applying pattern rule {rule.name}: {e}",
                                exc_info=True
                            )
                        ins = ins.next

        # Post-pass hook
        if self.post_pass_hook:
            self.post_pass_hook(context, total_changes)

        # Save to cache (if enabled)
        if self.cache_saver and total_changes > 0:
            self.cache_saver(mba, maturity, total_changes)

        logger.info(f"Optimization pass at maturity {maturity}: {total_changes} total changes")
        return total_changes

    def get_statistics(self) -> OptimizationStatistics:
        """Get current optimization statistics."""
        return self.statistics

    def reset_statistics(self) -> None:
        """Reset statistics counters."""
        self.statistics = OptimizationStatistics()
        logger.debug("Statistics reset")

    def set_cache_handlers(self, loader=None, saver=None) -> None:
        """Set cache loading and saving handlers.

        This is a hook point for implementing persistent caching
        (see Phase 4 of the performance optimization plan).

        Args:
            loader: Callable that takes (mba, maturity) and returns cached changes or None.
            saver: Callable that takes (mba, maturity, changes) and saves to cache.
        """
        self.cache_loader = loader
        self.cache_saver = saver
        logger.info("Cache handlers configured")

    def set_profiling_hooks(self, pre_hook=None, post_hook=None) -> None:
        """Set profiling hooks for performance measurement.

        Args:
            pre_hook: Called before each optimization pass with (context).
            post_hook: Called after each optimization pass with (context, changes).
        """
        self.pre_pass_hook = pre_hook
        self.post_pass_hook = post_hook
        logger.info("Profiling hooks configured")


def create_default_manager(config: Dict[str, Any] | None = None) -> OptimizerManager:
    """Factory function to create a manager with default configuration.

    This is a convenience function for common use cases.

    Args:
        config: Optional configuration dictionary. Defaults to empty dict.

    Returns:
        Configured OptimizerManager instance.
    """
    if config is None:
        config = {}

    manager = OptimizerManager(config)

    # TODO: Auto-discover and register default rules
    # This would scan d810.optimizers.microcode for rule classes

    return manager
