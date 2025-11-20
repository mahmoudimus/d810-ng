"""Test assertion helpers for structural deobfuscation verification.

This module provides assertion helpers that check deobfuscation quality
using instrumentation data from DeobfuscationContext.

Instead of brittle string matching, these assertions verify structural
properties of the deobfuscation:
- Which rules fired
- How many changes were made
- CFG transformations
- Pattern matching statistics

Example:
    >>> ctx = get_deobfuscation_context()
    >>> assert_rule_fired(ctx, "UnflattenerTigress")
    >>> assert_edges_unflattened(ctx, min_count=10)
    >>> assert_pattern_simplified(ctx, "xor", min_count=5)
"""

from typing import List, Optional

from src.d810.optimizers.instrumentation import DeobfuscationContext


class DeobfuscationAssertionError(AssertionError):
    """Custom exception for deobfuscation assertions with helpful messages."""
    pass


def assert_rule_fired(ctx: DeobfuscationContext, rule_name: str, message: Optional[str] = None):
    """Assert that a specific rule fired at least once.

    Args:
        ctx: The deobfuscation context
        rule_name: Name of the rule to check
        message: Optional custom error message

    Raises:
        DeobfuscationAssertionError: If the rule did not fire
    """
    if not ctx.rule_fired(rule_name):
        error_msg = message or (
            f"Expected rule '{rule_name}' to fire, but it did not.\n"
            f"Rules that fired: {list(ctx.rules_fired.keys())}"
        )
        raise DeobfuscationAssertionError(error_msg)


def assert_rule_not_fired(ctx: DeobfuscationContext, rule_name: str, message: Optional[str] = None):
    """Assert that a specific rule did not fire.

    Args:
        ctx: The deobfuscation context
        rule_name: Name of the rule to check
        message: Optional custom error message

    Raises:
        DeobfuscationAssertionError: If the rule fired
    """
    if ctx.rule_fired(rule_name):
        fire_count = ctx.rule_fire_count(rule_name)
        changes = ctx.total_changes_by_rule(rule_name)
        error_msg = message or (
            f"Expected rule '{rule_name}' NOT to fire, but it fired {fire_count} times "
            f"and made {changes} changes."
        )
        raise DeobfuscationAssertionError(error_msg)


def assert_rule_fire_count(
    ctx: DeobfuscationContext,
    rule_name: str,
    expected_count: int,
    message: Optional[str] = None
):
    """Assert that a rule fired an exact number of times.

    Args:
        ctx: The deobfuscation context
        rule_name: Name of the rule to check
        expected_count: Expected number of times the rule should fire
        message: Optional custom error message

    Raises:
        DeobfuscationAssertionError: If fire count doesn't match
    """
    actual_count = ctx.rule_fire_count(rule_name)
    if actual_count != expected_count:
        error_msg = message or (
            f"Expected rule '{rule_name}' to fire {expected_count} times, "
            f"but it fired {actual_count} times."
        )
        raise DeobfuscationAssertionError(error_msg)


def assert_minimum_changes(
    ctx: DeobfuscationContext,
    rule_name: str,
    min_changes: int,
    message: Optional[str] = None
):
    """Assert that a rule made at least a certain number of changes.

    Args:
        ctx: The deobfuscation context
        rule_name: Name of the rule to check
        min_changes: Minimum expected changes
        message: Optional custom error message

    Raises:
        DeobfuscationAssertionError: If changes are below minimum
    """
    actual_changes = ctx.total_changes_by_rule(rule_name)
    if actual_changes < min_changes:
        error_msg = message or (
            f"Expected rule '{rule_name}' to make at least {min_changes} changes, "
            f"but it only made {actual_changes} changes."
        )
        raise DeobfuscationAssertionError(error_msg)


def assert_flow_rule_fired(
    ctx: DeobfuscationContext,
    message: Optional[str] = None
):
    """Assert that at least one flow optimization rule fired.

    Args:
        ctx: The deobfuscation context
        message: Optional custom error message

    Raises:
        DeobfuscationAssertionError: If no flow rules fired
    """
    flow_rules = ctx.flow_rules_that_fired()
    if not flow_rules:
        error_msg = message or (
            "Expected at least one flow optimization rule to fire, but none did.\n"
            f"Total rules that fired: {len(ctx.rules_fired)}"
        )
        raise DeobfuscationAssertionError(error_msg)


def assert_unflattening_occurred(
    ctx: DeobfuscationContext,
    min_edges: int = 1,
    message: Optional[str] = None
):
    """Assert that control flow unflattening occurred.

    Args:
        ctx: The deobfuscation context
        min_edges: Minimum number of edges that should be unflattened
        message: Optional custom error message

    Raises:
        DeobfuscationAssertionError: If unflattening didn't occur
    """
    if not ctx.unflattening_occurred():
        error_msg = message or (
            "Expected control flow unflattening to occur, but no unflattener rules fired.\n"
            f"Flow rules that fired: {ctx.flow_rules_that_fired()}"
        )
        raise DeobfuscationAssertionError(error_msg)

    edges = ctx.edges_unflattened()
    if edges < min_edges:
        error_msg = message or (
            f"Expected at least {min_edges} edges to be unflattened, "
            f"but only {edges} were unflattened."
        )
        raise DeobfuscationAssertionError(error_msg)


def assert_edges_redirected(
    ctx: DeobfuscationContext,
    min_count: int,
    max_count: Optional[int] = None,
    message: Optional[str] = None
):
    """Assert that a certain number of CFG edges were redirected.

    Args:
        ctx: The deobfuscation context
        min_count: Minimum expected edge redirections
        max_count: Optional maximum expected edge redirections
        message: Optional custom error message

    Raises:
        DeobfuscationAssertionError: If edge count is out of range
    """
    actual_count = ctx.cfg_stats.edges_redirected
    if actual_count < min_count:
        error_msg = message or (
            f"Expected at least {min_count} edges to be redirected, "
            f"but only {actual_count} were redirected."
        )
        raise DeobfuscationAssertionError(error_msg)

    if max_count is not None and actual_count > max_count:
        error_msg = message or (
            f"Expected at most {max_count} edges to be redirected, "
            f"but {actual_count} were redirected."
        )
        raise DeobfuscationAssertionError(error_msg)


def assert_switch_cases_reduced(
    ctx: DeobfuscationContext,
    min_reduction: int = 1,
    message: Optional[str] = None
):
    """Assert that switch cases were reduced (control flow unflattening).

    Args:
        ctx: The deobfuscation context
        min_reduction: Minimum expected reduction in switch cases
        message: Optional custom error message

    Raises:
        DeobfuscationAssertionError: If switch cases weren't reduced enough
    """
    delta = ctx.cfg_stats.switch_cases_delta()
    if delta >= 0:
        # Cases increased or stayed same
        error_msg = message or (
            f"Expected switch cases to be reduced, but they went from "
            f"{ctx.cfg_stats.switch_cases_initial} to {ctx.cfg_stats.switch_cases_final} "
            f"(Δ{delta})."
        )
        raise DeobfuscationAssertionError(error_msg)

    reduction = -delta  # Make positive for comparison
    if reduction < min_reduction:
        error_msg = message or (
            f"Expected at least {min_reduction} switch cases to be removed, "
            f"but only {reduction} were removed "
            f"({ctx.cfg_stats.switch_cases_initial} → {ctx.cfg_stats.switch_cases_final})."
        )
        raise DeobfuscationAssertionError(error_msg)


def assert_pattern_simplified(
    ctx: DeobfuscationContext,
    pattern_type: str,
    min_count: int = 1,
    message: Optional[str] = None
):
    """Assert that a specific pattern type was simplified.

    Args:
        ctx: The deobfuscation context
        pattern_type: Type of pattern (xor, and, or, neg, mba, constant)
        min_count: Minimum expected pattern matches
        message: Optional custom error message

    Raises:
        DeobfuscationAssertionError: If pattern wasn't simplified enough
    """
    actual_count = ctx.pattern_matches_by_type(pattern_type)
    if actual_count < min_count:
        error_msg = message or (
            f"Expected at least {min_count} '{pattern_type}' patterns to be simplified, "
            f"but only {actual_count} were simplified."
        )
        raise DeobfuscationAssertionError(error_msg)


def assert_total_changes(
    ctx: DeobfuscationContext,
    min_changes: int,
    max_changes: Optional[int] = None,
    message: Optional[str] = None
):
    """Assert that total optimization changes are within expected range.

    Args:
        ctx: The deobfuscation context
        min_changes: Minimum expected total changes
        max_changes: Optional maximum expected changes
        message: Optional custom error message

    Raises:
        DeobfuscationAssertionError: If total changes are out of range
    """
    actual_changes = ctx.total_changes()
    if actual_changes < min_changes:
        error_msg = message or (
            f"Expected at least {min_changes} total changes, "
            f"but only {actual_changes} changes were made."
        )
        raise DeobfuscationAssertionError(error_msg)

    if max_changes is not None and actual_changes > max_changes:
        error_msg = message or (
            f"Expected at most {max_changes} total changes, "
            f"but {actual_changes} changes were made."
        )
        raise DeobfuscationAssertionError(error_msg)


def assert_deobfuscation_improved_code(
    ctx: DeobfuscationContext,
    message: Optional[str] = None
):
    """Assert that deobfuscation actually improved the code.

    This is a high-level assertion that checks:
    - At least some rules fired
    - At least some changes were made
    - Either flow or pattern rules were active

    Args:
        ctx: The deobfuscation context
        message: Optional custom error message

    Raises:
        DeobfuscationAssertionError: If no meaningful deobfuscation occurred
    """
    if not ctx.rules_fired:
        error_msg = message or "No optimization rules fired - deobfuscation did not run."
        raise DeobfuscationAssertionError(error_msg)

    total_changes = ctx.total_changes()
    if total_changes == 0:
        error_msg = message or (
            f"Optimization rules fired ({len(ctx.rules_fired)} rules) but made 0 changes. "
            "This suggests either:\n"
            "1. Code was already deobfuscated\n"
            "2. Rules failed to match obfuscated patterns\n"
            "3. Configuration issue preventing optimizations"
        )
        raise DeobfuscationAssertionError(error_msg)


def get_deobfuscation_summary(ctx: DeobfuscationContext) -> str:
    """Get a human-readable summary of deobfuscation for test output.

    Args:
        ctx: The deobfuscation context

    Returns:
        Multi-line string summary
    """
    summary = ctx.get_summary()

    lines = [
        "=" * 80,
        "DEOBFUSCATION SUMMARY",
        "=" * 80,
    ]

    if summary['function']['name']:
        lines.append(f"Function: {summary['function']['name']} @ {summary['function']['address']}")

    lines.extend([
        "",
        f"Total Changes: {summary['execution']['total_changes']}",
        f"Rules Fired: {summary['execution']['total_rules_fired']}",
        f"  - Flow Rules: {summary['rules']['flow_rules']}",
        f"  - Pattern Rules: {summary['rules']['pattern_rules']}",
        "",
        "Top Rules:",
    ])

    # Sort rules by changes
    sorted_rules = sorted(
        summary['rules']['by_rule'].items(),
        key=lambda x: x[1]['total_changes'],
        reverse=True
    )[:10]

    for rule_name, stats in sorted_rules:
        lines.append(f"  {rule_name}: {stats['total_changes']} changes ({stats['fire_count']}x)")

    cfg = summary['cfg']
    lines.extend([
        "",
        "CFG Changes:",
        f"  Blocks: {cfg['blocks']['initial']} → {cfg['blocks']['final']} (Δ{cfg['blocks']['delta']})",
        f"  Edges Redirected: {cfg['edges']['redirected']}",
        f"  Dispatchers Found: {cfg['control_flow']['dispatchers_found']}",
        f"  Switch Cases: {cfg['control_flow']['switch_cases_initial']} → {cfg['control_flow']['switch_cases_final']}",
    ])

    patterns = summary['patterns']
    if any(patterns.values()):
        lines.extend([
            "",
            "Pattern Simplifications:",
            f"  XOR: {patterns['xor']}",
            f"  AND: {patterns['and']}",
            f"  OR: {patterns['or']}",
            f"  NEG: {patterns['neg']}",
            f"  MBA: {patterns['mba']}",
            f"  Constants: {patterns['constant']}",
        ])

    lines.append("=" * 80)

    return "\n".join(lines)
