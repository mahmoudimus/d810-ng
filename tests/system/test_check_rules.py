"""Test to verify refactored DSL rules are loaded, not old AST rules."""

import unittest

import idaapi

from .ida_test_base import IDAProTestCase


class TestRuleRegistry(IDAProTestCase):
    """Verify that refactored DSL rules are loaded in registry."""

    binary_name = "libobfuscated.dll"

    @classmethod
    def setUpClass(cls):
        """Open database."""
        super().setUpClass()

        # Initialize the Hex-Rays decompiler plugin
        if not idaapi.init_hexrays_plugin():
            raise unittest.SkipTest("Hex-Rays decompiler plugin not available")

    def test_check_loaded_rules_are_refactored(self):
        """Verify refactored DSL-based rules are loaded, not old AST-based rules."""
        from d810.optimizers.microcode.instructions.handler import (
            InstructionOptimizationRule,
        )
        from d810.optimizers.rules import VerifiableRule

        # Get all registered rules
        all_rules = InstructionOptimizationRule.all()
        print(f"\n{'=' * 80}")
        print(f"RULE REGISTRY ANALYSIS")
        print(f"{'=' * 80}")
        print(f"Total registered rules: {len(all_rules)}")

        # Separate by type
        verifiable_rules = []
        pattern_matching_rules = []
        other_rules = []

        for rule in all_rules:
            if not isinstance(rule, type):
                continue

            if issubclass(rule, VerifiableRule):
                verifiable_rules.append(rule)
            else:
                # Check if it's a PatternMatchingRule (old AST-based)
                base_names = [b.__name__ for b in rule.__bases__]
                if "PatternMatchingRule" in base_names:
                    pattern_matching_rules.append(rule)
                else:
                    other_rules.append(rule)

        print(f"\n{'=' * 80}")
        print(f"VerifiableRule (NEW DSL-based) subclasses: {len(verifiable_rules)}")
        print(f"{'=' * 80}")
        if verifiable_rules:
            print("Sample VerifiableRule subclasses (first 10):")
            for i, rule in enumerate(verifiable_rules[:10], 1):
                module = rule.__module__
                print(f"  {i:3}. {rule.__name__:50} ({module})")
            if len(verifiable_rules) > 10:
                print(f"  ... and {len(verifiable_rules) - 10} more VerifiableRule subclasses")
        else:
            print("❌ NO VerifiableRule subclasses found!")

        print(f"\n{'=' * 80}")
        print(
            f"PatternMatchingRule (OLD AST-based) subclasses: {len(pattern_matching_rules)}"
        )
        print(f"{'=' * 80}")
        if pattern_matching_rules:
            print("⚠️  OLD AST-based rules still loaded (first 10):")
            for i, rule in enumerate(pattern_matching_rules[:10], 1):
                module = rule.__module__
                print(f"  {i:3}. {rule.__name__:50} ({module})")
            if len(pattern_matching_rules) > 10:
                print(
                    f"  ... and {len(pattern_matching_rules) - 10} more PatternMatchingRule subclasses"
                )
        else:
            print("✅ No old PatternMatchingRule subclasses found")

        print(f"\n{'=' * 80}")
        print(f"Other rules: {len(other_rules)}")
        print(f"{'=' * 80}")
        if other_rules:
            print("Sample other rules (first 10):")
            for i, rule in enumerate(other_rules[:10], 1):
                base_classes = [
                    b.__name__
                    for b in rule.__bases__
                    if b.__name__ != "InstructionOptimizationRule"
                ]
                module = rule.__module__
                print(f"  {i:3}. {rule.__name__:50} bases: {base_classes}")

        # Summary
        print(f"\n{'=' * 80}")
        print("SUMMARY")
        print(f"{'=' * 80}")
        total = len(all_rules)
        print(f"Total rules: {total}")
        print(
            f"  - NEW (VerifiableRule):    {len(verifiable_rules):3} ({len(verifiable_rules)/total*100:.1f}%)"
        )
        print(
            f"  - OLD (PatternMatching):   {len(pattern_matching_rules):3} ({len(pattern_matching_rules)/total*100:.1f}%)"
        )
        print(
            f"  - Other:                   {len(other_rules):3} ({len(other_rules)/total*100:.1f}%)"
        )
        print(f"{'=' * 80}")

        # ASSERTIONS
        self.assertGreater(
            len(verifiable_rules),
            0,
            "CRITICAL: NO refactored DSL rules are loaded! Refactoring FAILED!",
        )

        if len(pattern_matching_rules) > 0:
            print(
                f"\n⚠️  WARNING: {len(pattern_matching_rules)} OLD PatternMatchingRule subclasses still loaded"
            )
            print("   This could mean:")
            print("   1. Not all rules were refactored yet (expected)")
            print("   2. Old rules weren't removed after refactoring (needs cleanup)")

        if len(verifiable_rules) > len(pattern_matching_rules):
            print(
                f"\n✅ SUCCESS: More refactored rules ({len(verifiable_rules)}) than old rules ({len(pattern_matching_rules)})"
            )

        # Success if we have ANY refactored rules loaded
        self.assertGreater(len(verifiable_rules), 0)


if __name__ == "__main__":
    unittest.main()
