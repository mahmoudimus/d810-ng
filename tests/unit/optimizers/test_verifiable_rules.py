"""Automated verification tests for all VerifiableRule subclasses.

This test module demonstrates the power of the refactored rule system:
- No manual test cases needed for individual rules
- Rules verify themselves using Z3
- Adding a new rule automatically adds it to the test suite
- Failed verification provides detailed counterexamples

The single test function below replaces what would have been dozens of manual
test cases in the old system.
"""

import pytest

from d810.optimizers.rules import RULE_REGISTRY, VerifiableRule

# Import all refactored rule modules to populate the registry
# As you refactor more rules, add them here
try:
    import d810.optimizers.microcode.instructions.pattern_matching.rewrite_xor_refactored
    import d810.optimizers.microcode.instructions.pattern_matching.rewrite_neg_refactored
except ImportError as e:
    # If running in an environment without IDA, some imports might fail
    # The test will be skipped if no rules are registered
    pass


class TestVerifiableRules:
    """Test suite for verifiable optimization rules."""

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

        Args:
            rule: A VerifiableRule instance (provided by pytest parametrization).

        Raises:
            AssertionError: If the rule's pattern and replacement are not equivalent.
        """
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
# 1. Import the module containing it in this file
# 2. The rule is automatically added to RULE_REGISTRY
# 3. All three tests above automatically apply to it
# 4. No additional test code needs to be written!
#
# This is the power of the refactored architecture:
# - Rules are self-verifying
# - Tests are generic and comprehensive
# - Adding rules is trivial and safe
