"""Automated verification tests for all VerifiableRule subclasses.

This test module demonstrates the power of the refactored rule system:
- No manual test cases needed for individual rules
- Rules verify themselves using Z3
- Adding a new rule automatically adds it to the test suite
- Failed verification provides detailed counterexamples

The single test function below replaces what would have been dozens of manual
test cases in the old system.

NOTE: Rules are automatically discovered and loaded by the conftest.py
      fixture using the d810 scanner infrastructure. No manual imports needed!
"""

import pytest

from d810.optimizers.rules import RULE_REGISTRY, VerifiableRule


@pytest.mark.slow  # Z3 verification takes ~12 seconds
class TestVerifiableRules:
    """Test suite for verifiable optimization rules.

    NOTE: These tests only require Z3 and Python, NOT IDA Pro!
    The verification is pure symbolic math - no IDA needed.

    However, importing rule modules currently requires IDA because
    they import from d810.hexrays.hexrays_helpers (which imports ida_hexrays).
    After MBA package separation, these will be pure_python tests.
    """

    def test_registry_is_populated(self):
        """Sanity check: ensure at least some rules were discovered and registered.

        If this fails, it means either:
        1. No refactored rule modules were imported
        2. The auto-registration mechanism is broken
        3. All rule classes are abstract (have unimplemented abstract methods)
        """
        assert len(RULE_REGISTRY) > 0, (
            "No rules were discovered and registered. "
            "Make sure refactored rule modules are imported in this test file."
        )

    @pytest.mark.parametrize("rule", RULE_REGISTRY, ids=lambda r: r.name)
    def test_rule_is_correct(self, rule: VerifiableRule):
        """Verify the mathematical correctness of every registered rule.

        This single, generic test verifies every rule that inherits from
        VerifiableRule by calling its verify() method, which uses Z3 to
        prove semantic equivalence.

        If this test fails for a rule, it means:
        - The pattern and replacement are NOT semantically equivalent
        - The rule would introduce bugs if used
        - The rule definition needs to be fixed

        The failure message will include:
        - Rule name and description
        - The incorrect identity being claimed
        - A concrete counterexample showing inputs where pattern ≠ replacement

        Rules can be marked with:
        - KNOWN_INCORRECT = True: Rule is mathematically incorrect (will be skipped)
        - SKIP_VERIFICATION = True: Rule has constraints that can't be verified with Z3 (will be skipped)

        Args:
            rule: A VerifiableRule instance (provided by pytest parametrization).

        Raises:
            AssertionError: If the rule's pattern and replacement are not equivalent.
        """
        # Check if this rule should be skipped
        if getattr(rule, 'KNOWN_INCORRECT', False):
            pytest.skip(f"Rule {rule.name} is marked as KNOWN_INCORRECT (mathematically incorrect)")

        if getattr(rule, 'SKIP_VERIFICATION', False):
            pytest.skip(f"Rule {rule.name} is marked as SKIP_VERIFICATION (has size-dependent constraints)")

        # The verification logic and error reporting are handled inside the rule itself
        # This keeps the test clean and the failure output rich with context
        rule.verify()

    def test_rule_names_are_unique(self):
        """Ensure all rules have unique names.

        Duplicate names would cause confusion in logging and debugging.
        """
        names = [rule.name for rule in RULE_REGISTRY]
        duplicates = [name for name in names if names.count(name) > 1]

        assert len(duplicates) == 0, (
            f"Found rules with duplicate names: {set(duplicates)}\n"
            f"Each rule must have a unique name for identification."
        )

    def test_all_rules_have_descriptions(self):
        """Ensure all rules have meaningful descriptions.

        Rules should document what they do and why. A description is required
        for maintainability.
        """
        unnamed_rules = [
            rule for rule in RULE_REGISTRY
            if rule.description in ["No description", ""]
        ]

        assert len(unnamed_rules) == 0, (
            f"Found rules without descriptions: {[r.name for r in unnamed_rules]}\n"
            f"Every rule should have a description explaining what it does."
        )


# When a developer adds a new VerifiableRule subclass:
# 1. Create the rule class in a module under pattern_matching/
# 2. The scanner automatically discovers and loads it (via conftest.py)
# 3. The rule is automatically added to RULE_REGISTRY via __init_subclass__
# 4. All three tests above automatically apply to it
# 5. No additional test code or imports needed!
#
# This is the power of the refactored architecture:
# - Rules are self-verifying (Z3 proves correctness)
# - Tests are generic and comprehensive
# - Scanner automatically discovers new rules
# - Adding rules is trivial and safe (no manual test updates)
