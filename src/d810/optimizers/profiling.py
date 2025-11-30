"""Profiling infrastructure for identifying optimization bottlenecks.

This module implements Phase 4 (part 1) of the performance optimization plan:
profiling and bottleneck identification. It provides instrumentation to measure
where time is being spent during microcode optimization.

The profiling system integrates with OptimizerManager via hooks and provides:
- Per-rule timing
- Per-pass timing
- Aggregated statistics
- HTML/JSON reports

Usage:
    profiler = OptimizationProfiler()
    manager.set_profiling_hooks(
        pre_hook=profiler.start_pass,
        post_hook=profiler.end_pass
    )

    # After optimization
    report = profiler.generate_report()
    profiler.save_html_report("profile.html")
"""

from __future__ import annotations

import json
import time
from collections import defaultdict
from dataclasses import dataclass, field
from typing import Any, Dict, List

from d810.conf.loggers import getLogger
from d810.optimizers.core import OptimizationContext

logger = getLogger("D810.profiling")


@dataclass
class RuleProfile:
    """Profiling data for a single rule."""
    name: str
    total_time: float = 0.0
    call_count: int = 0
    changes_made: int = 0
    avg_time_per_call: float = 0.0
    time_percentage: float = 0.0

    def update_averages(self, total_time_all_rules: float):
        """Calculate derived statistics."""
        if self.call_count > 0:
            self.avg_time_per_call = self.total_time / self.call_count
        if total_time_all_rules > 0:
            self.time_percentage = (self.total_time / total_time_all_rules) * 100


@dataclass
class PassProfile:
    """Profiling data for a single optimization pass."""
    maturity: int
    start_time: float
    end_time: float
    duration: float = 0.0
    changes_made: int = 0
    rules_executed: int = 0


class OptimizationProfiler:
    """Profiler for measuring optimization performance.

    This profiler hooks into OptimizerManager to collect timing data
    for each rule and pass. It identifies bottlenecks and generates
    reports for performance optimization.

    The profiler tracks:
    - Time spent in each rule
    - Number of times each rule is called
    - Changes made by each rule
    - Total pass duration
    - Rule call sequences

    Example:
        >>> profiler = OptimizationProfiler()
        >>> manager.set_profiling_hooks(
        ...     pre_hook=profiler.start_pass,
        ...     post_hook=profiler.end_pass
        ... )
        >>>
        >>> # ... run optimizations ...
        >>>
        >>> # Generate report
        >>> report = profiler.generate_report()
        >>> for rule in report['top_rules_by_time']:
        ...     print(f"{rule.name}: {rule.total_time:.3f}s")
    """

    def __init__(self):
        """Initialize the profiler."""
        self.rule_profiles: Dict[str, RuleProfile] = {}
        self.pass_profiles: List[PassProfile] = []
        self.current_pass: PassProfile | None = None
        self.current_rule_start: float | None = None
        self.current_rule_name: str | None = None
        self.enabled = True

    def start_pass(self, context: OptimizationContext) -> None:
        """Called at the start of each optimization pass.

        This is the pre_hook for OptimizerManager.

        Args:
            context: The optimization context for this pass.
        """
        if not self.enabled:
            return

        self.current_pass = PassProfile(
            maturity=context.maturity,
            start_time=time.perf_counter(),
            end_time=0.0
        )
        logger.debug(f"Starting profiling for maturity {context.maturity}")

    def end_pass(self, context: OptimizationContext, changes: int) -> None:
        """Called at the end of each optimization pass.

        This is the post_hook for OptimizerManager.

        Args:
            context: The optimization context for this pass.
            changes: Number of changes made during the pass.
        """
        if not self.enabled or self.current_pass is None:
            return

        self.current_pass.end_time = time.perf_counter()
        self.current_pass.duration = self.current_pass.end_time - self.current_pass.start_time
        self.current_pass.changes_made = changes

        self.pass_profiles.append(self.current_pass)
        logger.info(
            f"Pass at maturity {context.maturity}: "
            f"{self.current_pass.duration:.3f}s, {changes} changes"
        )
        self.current_pass = None

    def start_rule(self, rule_name: str) -> None:
        """Mark the start of a rule execution.

        Call this before applying a rule.

        Args:
            rule_name: Name of the rule being applied.
        """
        if not self.enabled:
            return

        self.current_rule_name = rule_name
        self.current_rule_start = time.perf_counter()

        # Ensure profile exists
        if rule_name not in self.rule_profiles:
            self.rule_profiles[rule_name] = RuleProfile(name=rule_name)

    def end_rule(self, rule_name: str, changes: int = 0) -> None:
        """Mark the end of a rule execution.

        Call this after applying a rule.

        Args:
            rule_name: Name of the rule that was applied.
            changes: Number of changes the rule made.
        """
        if not self.enabled or self.current_rule_start is None:
            return

        duration = time.perf_counter() - self.current_rule_start
        profile = self.rule_profiles[rule_name]
        profile.total_time += duration
        profile.call_count += 1
        profile.changes_made += changes

        if self.current_pass:
            self.current_pass.rules_executed += 1

        self.current_rule_name = None
        self.current_rule_start = None

    def generate_report(self) -> Dict[str, Any]:
        """Generate a comprehensive profiling report.

        Returns:
            Dictionary containing profiling data:
            - total_time: Total optimization time
            - total_passes: Number of optimization passes
            - total_changes: Total changes made
            - rule_profiles: List of RuleProfile objects
            - top_rules_by_time: Top 10 rules by time
            - top_rules_by_changes: Top 10 rules by changes
            - pass_summaries: Summary of each pass
        """
        # Calculate total time
        total_time = sum(p.duration for p in self.pass_profiles)

        # Update derived statistics
        for profile in self.rule_profiles.values():
            profile.update_averages(total_time)

        # Sort rules by various metrics
        rules_by_time = sorted(
            self.rule_profiles.values(),
            key=lambda r: r.total_time,
            reverse=True
        )

        rules_by_changes = sorted(
            self.rule_profiles.values(),
            key=lambda r: r.changes_made,
            reverse=True
        )

        return {
            'total_time': total_time,
            'total_passes': len(self.pass_profiles),
            'total_changes': sum(p.changes_made for p in self.pass_profiles),
            'rule_profiles': list(self.rule_profiles.values()),
            'top_rules_by_time': rules_by_time[:10],
            'top_rules_by_changes': rules_by_changes[:10],
            'pass_summaries': self.pass_profiles,
        }

    def save_json_report(self, filename: str) -> None:
        """Save profiling report as JSON.

        Args:
            filename: Output filename.
        """
        report = self.generate_report()

        # Convert dataclasses to dictionaries
        json_report = {
            'total_time': report['total_time'],
            'total_passes': report['total_passes'],
            'total_changes': report['total_changes'],
            'rules': [
                {
                    'name': r.name,
                    'total_time': r.total_time,
                    'call_count': r.call_count,
                    'changes_made': r.changes_made,
                    'avg_time_per_call': r.avg_time_per_call,
                    'time_percentage': r.time_percentage,
                }
                for r in report['rule_profiles']
            ],
            'passes': [
                {
                    'maturity': p.maturity,
                    'duration': p.duration,
                    'changes_made': p.changes_made,
                    'rules_executed': p.rules_executed,
                }
                for p in report['pass_summaries']
            ]
        }

        with open(filename, 'w') as f:
            json.dump(json_report, f, indent=2)

        logger.info(f"Saved JSON profiling report to {filename}")

    def save_html_report(self, filename: str) -> None:
        """Save profiling report as HTML.

        Args:
            filename: Output filename.
        """
        report = self.generate_report()

        html = f"""<!DOCTYPE html>
<html>
<head>
    <title>D810 Optimization Profile</title>
    <style>
        body {{ font-family: Arial, sans-serif; margin: 20px; }}
        h1, h2 {{ color: #333; }}
        table {{ border-collapse: collapse; width: 100%; margin: 20px 0; }}
        th, td {{ border: 1px solid #ddd; padding: 8px; text-align: left; }}
        th {{ background-color: #4CAF50; color: white; }}
        tr:nth-child(even) {{ background-color: #f2f2f2; }}
        .summary {{ background-color: #e7f3fe; padding: 15px; border-left: 6px solid #2196F3; margin: 20px 0; }}
        .metric {{ font-weight: bold; color: #2196F3; }}
    </style>
</head>
<body>
    <h1>D810 Optimization Profile</h1>

    <div class="summary">
        <p><span class="metric">Total Time:</span> {report['total_time']:.3f} seconds</p>
        <p><span class="metric">Total Passes:</span> {report['total_passes']}</p>
        <p><span class="metric">Total Changes:</span> {report['total_changes']}</p>
    </div>

    <h2>Top Rules by Time</h2>
    <table>
        <tr>
            <th>Rule</th>
            <th>Time (s)</th>
            <th>Percentage</th>
            <th>Calls</th>
            <th>Avg Time/Call (ms)</th>
            <th>Changes</th>
        </tr>
"""

        for rule in report['top_rules_by_time']:
            html += f"""        <tr>
            <td>{rule.name}</td>
            <td>{rule.total_time:.3f}</td>
            <td>{rule.time_percentage:.1f}%</td>
            <td>{rule.call_count}</td>
            <td>{rule.avg_time_per_call * 1000:.2f}</td>
            <td>{rule.changes_made}</td>
        </tr>
"""

        html += """    </table>

    <h2>Pass Summary</h2>
    <table>
        <tr>
            <th>Maturity</th>
            <th>Duration (s)</th>
            <th>Changes</th>
            <th>Rules Executed</th>
        </tr>
"""

        for pass_prof in report['pass_summaries']:
            html += f"""        <tr>
            <td>{pass_prof.maturity}</td>
            <td>{pass_prof.duration:.3f}</td>
            <td>{pass_prof.changes_made}</td>
            <td>{pass_prof.rules_executed}</td>
        </tr>
"""

        html += """    </table>
</body>
</html>"""

        with open(filename, 'w') as f:
            f.write(html)

        logger.info(f"Saved HTML profiling report to {filename}")

    def reset(self) -> None:
        """Reset all profiling data."""
        self.rule_profiles = {}
        self.pass_profiles = []
        self.current_pass = None
        logger.debug("Profiler reset")

    def print_summary(self) -> None:
        """Print a text summary to the console."""
        report = self.generate_report()

        print("\n" + "="*60)
        print("D810 OPTIMIZATION PROFILE")
        print("="*60)
        print(f"Total Time: {report['total_time']:.3f}s")
        print(f"Total Passes: {report['total_passes']}")
        print(f"Total Changes: {report['total_changes']}")
        print("\nTop 10 Rules by Time:")
        print("-"*60)
        print(f"{'Rule':<30} {'Time (s)':<12} {'%':<8} {'Calls':<8}")
        print("-"*60)

        for rule in report['top_rules_by_time']:
            print(f"{rule.name:<30} {rule.total_time:<12.3f} {rule.time_percentage:<8.1f} {rule.call_count:<8}")

        print("="*60 + "\n")
