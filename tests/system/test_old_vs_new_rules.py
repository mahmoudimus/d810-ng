"""Test to compare OLD AST-based rules vs NEW DSL-based rules.

This test verifies behavioral equivalence between the old and new implementations:
1. Capture which rules fire with BOTH old and new rules loaded
2. Move old rules out of the way
3. Run again with ONLY new rules
4. Assert the same patterns are being matched
"""

import json
import unittest
from pathlib import Path

import idaapi
import idc

from .ida_test_base import IDAProTestCase
from .stutils import (
    d810_state,
    configure_hexrays_for_consistent_output,
    setup_libobfuscated_function_names,
)


class TestOldVsNewRules(IDAProTestCase):
    """Compare rule firing between old and new implementations."""

    binary_name = "libobfuscated.dll"

    @classmethod
    def setUpClass(cls):
        """Open database and initialize Hex-Rays."""
        super().setUpClass()

        # Initialize the Hex-Rays decompiler plugin
        if not idaapi.init_hexrays_plugin():
            raise unittest.SkipTest("Hex-Rays decompiler plugin not available")

        # Configure Hex-Rays for consistent output
        configure_hexrays_for_consistent_output()

        # Set up function names
        setup_libobfuscated_function_names()

    def test_capture_old_plus_new_rule_firing(self):
        """Capture which rules fire when BOTH old and new rules are loaded.

        This is the baseline - with duplicate rules, we'll see both old AST-based
        rules and new DSL-based rules firing.

        NOTE: OLD PatternMatchingRule rules use a different code path (PatternOptimizer)
        which doesn't use the instrumentation context. So we need to collect rule
        firing data from both sources:
        - Instrumentation context: For NEW refactored rules (Z3, VerifiableRule, etc.)
        - Optimizer usage stats: For OLD PatternMatchingRule rules
        """
        from d810.optimizers.instrumentation import get_current_deobfuscation_context
        from d810.optimizers.microcode.instructions.handler import (
            InstructionOptimizationRule,
        )
        from d810.optimizers.rules import VerifiableRule

        # First, check registry composition
        all_rules = InstructionOptimizationRule.all()
        verifiable_rules = [
            r for r in all_rules
            if isinstance(r, type) and issubclass(r, VerifiableRule)
        ]
        pattern_matching_rules = [
            r for r in all_rules
            if isinstance(r, type) and hasattr(r, '__bases__')
            and any(b.__name__ == 'PatternMatchingRule' for b in r.__bases__)
        ]

        print(f"\n{'=' * 80}")
        print(f"BASELINE: Testing with BOTH old and new rules loaded")
        print(f"{'=' * 80}")
        print(f"Total registered rules: {len(all_rules)}")
        print(f"  - NEW (VerifiableRule DSL-based): {len(verifiable_rules)}")
        print(f"  - OLD (PatternMatchingRule AST-based): {len(pattern_matching_rules)}")
        print(f"{'=' * 80}")

        # Test functions that exercise different rule types
        test_functions = [
            ("test_xor", "XOR pattern simplification"),
            ("test_chained_add", "Arithmetic chain simplification"),
            ("test_mba_guessing", "MBA pattern simplification"),
            ("test_opaque_predicate", "Opaque predicate removal"),
        ]

        results = {}

        for func_name, description in test_functions:
            func_ea = idc.get_name_ea_simple(func_name)
            if func_ea == idaapi.BADADDR:
                print(f"⚠️  Function '{func_name}' not found, skipping")
                continue

            print(f"\n📍 Testing {func_name} ({description})")

            with d810_state() as state:
                with state.for_project("example_libobfuscated.json"):
                    # Reset rule usage statistics before decompilation
                    state.manager.instruction_optimizer.reset_rule_usage_statistic()

                    # Decompile - this triggers optimization
                    decompiled = idaapi.decompile(func_ea, flags=idaapi.DECOMP_NO_CACHE)
                    self.assertIsNotNone(decompiled, f"Decompilation failed for {func_name}")

                    # Get instrumentation context (for NEW rules)
                    ctx = get_current_deobfuscation_context()

                    # Get OLD PatternMatchingRule usage from optimizer stats
                    pattern_optimizer_rules = {}
                    for ins_optimizer in state.manager.instruction_optimizer.instruction_optimizers:
                        if ins_optimizer.name == "PatternOptimizer":
                            pattern_optimizer_rules = {
                                name: count
                                for name, count in ins_optimizer.rules_usage_info.items()
                                if count > 0
                            }
                            break

            # Collect all rules that fired from BOTH sources
            all_rules_fired_set = set()
            old_rules_fired = []
            new_rules_fired = []

            # From PatternOptimizer (OLD rules)
            for rule_name in pattern_optimizer_rules:
                all_rules_fired_set.add(rule_name)
                old_rules_fired.append(rule_name)

            # From instrumentation context (NEW rules + others)
            if ctx is not None:
                for rule_name in ctx.rules_fired.keys():
                    all_rules_fired_set.add(rule_name)
                    # Check if this is a VerifiableRule (NEW)
                    is_new = any(
                        r.__name__ == rule_name and issubclass(r, VerifiableRule)
                        for r in all_rules
                        if isinstance(r, type)
                    )
                    if is_new:
                        new_rules_fired.append(rule_name)

            all_rules_fired = sorted(all_rules_fired_set)

            # Build rules detail from both sources
            rules_detail = {}
            for name in all_rules_fired:
                detail = {"fire_count": 0, "total_changes": 0}
                if name in pattern_optimizer_rules:
                    detail["fire_count"] = pattern_optimizer_rules[name]
                    detail["source"] = "PatternOptimizer (OLD)"
                elif ctx is not None and name in ctx.rules_fired:
                    detail["fire_count"] = ctx.rule_fire_count(name)
                    detail["total_changes"] = ctx.total_changes_by_rule(name)
                    detail["source"] = "Instrumentation (NEW or Other)"
                rules_detail[name] = detail

            total_changes = ctx.total_changes() if ctx else 0

            results[func_name] = {
                "description": description,
                "total_rules_fired": len(all_rules_fired),
                "total_changes": total_changes,
                "old_rules_fired": sorted(old_rules_fired),
                "new_rules_fired": sorted(new_rules_fired),
                "old_count": len(old_rules_fired),
                "new_count": len(new_rules_fired),
                "rules_detail": rules_detail
            }

            print(f"   ✓ Total rules fired: {len(all_rules_fired)}")
            print(f"   ✓ OLD rules fired: {len(old_rules_fired)}")
            print(f"   ✓ NEW rules fired: {len(new_rules_fired)}")
            print(f"   ✓ Total changes: {total_changes}")

        # Save results for comparison after removing old rules
        output_dir = Path("/home/user/d810-ng/tests/system")
        output_file = output_dir / "old_vs_new_baseline.json"

        with open(output_file, 'w') as f:
            json.dump(results, f, indent=2)

        print(f"\n{'=' * 80}")
        print(f"Baseline results saved to: {output_file}")
        print(f"{'=' * 80}\n")

        # Summary
        total_old_fired = sum(r['old_count'] for r in results.values())
        total_new_fired = sum(r['new_count'] for r in results.values())

        print(f"SUMMARY ACROSS ALL FUNCTIONS:")
        print(f"  - Total OLD rules that fired: {total_old_fired}")
        print(f"  - Total NEW rules that fired: {total_new_fired}")

        # Assertions
        self.assertGreater(total_old_fired, 0, "OLD rules should have fired (baseline)")

        # NOTE: We DON'T expect NEW rules to fire yet because:
        # 1. Both OLD and NEW rules are registered
        # 2. PatternOptimizer (OLD) matches first
        # 3. NEW refactored rules don't get a chance to match
        # This is the whole point - we need to remove OLD rules to let NEW ones work!

        if total_new_fired > 0:
            print(f"\n✅ Both OLD and NEW rules fired!")
            print(f"    This means some refactored rules are already active.")
        else:
            print(f"\n⚠️  Only OLD rules fired (NEW rules: 0)")
            print(f"    This is EXPECTED - OLD PatternMatchingRules match first.")
            print(f"    Next step: Remove OLD rules and verify NEW rules achieve same results")


if __name__ == "__main__":
    unittest.main()
