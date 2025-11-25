"""Unit tests for RuleRegistry class.

Tests the injectable registry system that enables:
- Unit testing without IDA (store classes, not instances)
- Custom registries for different contexts
- Lazy instantiation when IDA is available
"""

import pytest

from d810.mba.dsl import Var
from d810.mba.rules import RuleRegistry, VerifiableRule, RULE_REGISTRY


# Test variables
x, y = Var("x"), Var("y")


class TestRuleRegistry:
    """Tests for RuleRegistry class."""

    def test_registry_creation(self):
        """Test creating a new registry."""
        reg = RuleRegistry("test")
        assert reg.name == "test"
        assert len(reg) == 0

    def test_global_registry_exists(self):
        """Test that RULE_REGISTRY is a RuleRegistry instance."""
        assert isinstance(RULE_REGISTRY, RuleRegistry)
        assert RULE_REGISTRY.name == "global"

    def test_register_class_not_instance(self):
        """Test that registry stores classes, not instances."""
        reg = RuleRegistry("test")

        class TestRule(VerifiableRule, registry=reg):
            PATTERN = x + y
            REPLACEMENT = y + x
            DESCRIPTION = "Test"

        # Class should be registered
        assert TestRule in reg
        assert len(reg) == 1

        # Should be the class itself, not an instance
        for cls in reg:
            assert cls is TestRule
            assert isinstance(cls, type)

    def test_custom_registry_isolation(self):
        """Test that custom registry doesn't pollute global registry."""
        initial_global_count = len(RULE_REGISTRY)
        reg = RuleRegistry("isolated")

        class IsolatedRule(VerifiableRule, registry=reg):
            PATTERN = x - y
            REPLACEMENT = x + (-y)
            DESCRIPTION = "Isolated"

        # Should be in custom registry
        assert IsolatedRule in reg
        assert len(reg) == 1

        # Should NOT be in global registry
        assert IsolatedRule not in RULE_REGISTRY
        # Global registry count should be unchanged
        assert len(RULE_REGISTRY) == initial_global_count

    def test_unregister(self):
        """Test unregistering a rule class."""
        reg = RuleRegistry("test")

        class ToRemove(VerifiableRule, registry=reg):
            PATTERN = x ^ y
            REPLACEMENT = y ^ x
            DESCRIPTION = "To remove"

        assert ToRemove in reg
        assert reg.unregister(ToRemove) is True
        assert ToRemove not in reg
        assert len(reg) == 0

    def test_unregister_nonexistent(self):
        """Test unregistering a class that's not in registry."""
        reg = RuleRegistry("test")

        class NotRegistered(VerifiableRule, registry=RuleRegistry("other")):
            PATTERN = x & y
            REPLACEMENT = y & x
            DESCRIPTION = "Not registered"

        assert reg.unregister(NotRegistered) is False

    def test_clear(self):
        """Test clearing all rules from registry."""
        reg = RuleRegistry("test")

        class Rule1(VerifiableRule, registry=reg):
            PATTERN = x + y
            REPLACEMENT = y + x
            DESCRIPTION = "Rule 1"

        class Rule2(VerifiableRule, registry=reg):
            PATTERN = x - y
            REPLACEMENT = x + (-y)
            DESCRIPTION = "Rule 2"

        assert len(reg) == 2
        reg.clear()
        assert len(reg) == 0

    def test_iteration(self):
        """Test iterating over registry yields classes."""
        reg = RuleRegistry("test")

        class IterRule1(VerifiableRule, registry=reg):
            PATTERN = x | y
            REPLACEMENT = y | x
            DESCRIPTION = "Iter 1"

        class IterRule2(VerifiableRule, registry=reg):
            PATTERN = x & y
            REPLACEMENT = y & x
            DESCRIPTION = "Iter 2"

        classes = list(reg)
        assert len(classes) == 2
        assert IterRule1 in classes
        assert IterRule2 in classes

    def test_no_duplicate_registration(self):
        """Test that registering same class twice doesn't duplicate."""
        reg = RuleRegistry("test")

        class NoDupeRule(VerifiableRule, registry=reg):
            PATTERN = x ^ y
            REPLACEMENT = y ^ x
            DESCRIPTION = "No dupe"

        initial_count = len(reg)

        # Try to register again
        reg.register(NoDupeRule)
        reg.register(NoDupeRule)

        assert len(reg) == initial_count

    def test_repr(self):
        """Test string representation."""
        reg = RuleRegistry("my_registry")

        class ReprRule(VerifiableRule, registry=reg):
            PATTERN = x + y
            REPLACEMENT = y + x
            DESCRIPTION = "Repr test"

        s = repr(reg)
        assert "my_registry" in s
        assert "1 rules" in s


class TestInstantiateAll:
    """Tests for lazy instantiation."""

    def test_instantiate_returns_list(self):
        """Test instantiate_all returns list of instances."""
        # Note: This test may fail without IDA, but that's expected
        # The purpose is to test the API, not the actual instantiation
        reg = RuleRegistry("test")

        class InstRule(VerifiableRule, registry=reg):
            PATTERN = x + y
            REPLACEMENT = y + x
            DESCRIPTION = "Inst test"

        # Without IDA, instantiation will fail but should return empty list
        # (due to exception handling in instantiate_all)
        instances = reg.instantiate_all()
        assert isinstance(instances, list)

    def test_instantiate_caches_result(self):
        """Test that instantiate_all caches its result."""
        reg = RuleRegistry("test")

        class CacheRule(VerifiableRule, registry=reg):
            PATTERN = x - y
            REPLACEMENT = x + (-y)
            DESCRIPTION = "Cache test"

        # First call
        result1 = reg.instantiate_all()
        # Second call should return same list
        result2 = reg.instantiate_all()

        assert result1 is result2  # Same object (cached)

    def test_register_invalidates_cache(self):
        """Test that registering a new class invalidates the cache."""
        reg = RuleRegistry("test")

        class First(VerifiableRule, registry=reg):
            PATTERN = x + y
            REPLACEMENT = y + x
            DESCRIPTION = "First"

        # Populate cache
        result1 = reg.instantiate_all()

        class Second(VerifiableRule, registry=reg):
            PATTERN = x - y
            REPLACEMENT = x + (-y)
            DESCRIPTION = "Second"

        # Cache should be invalidated
        result2 = reg.instantiate_all()

        # Results should be different objects
        assert result1 is not result2
