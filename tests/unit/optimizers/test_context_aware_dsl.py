"""Tests for context-aware DSL extensions.

These tests verify that the context-aware DSL correctly handles:
1. Context providers (binding variables from instruction context)
2. Context constraints (checking destination properties)
3. Destination updates (modifying the instruction destination)
"""

import pytest


class TestDestinationHelpers:
    """Test destination inspection helpers."""

    def test_is_high_half_without_ida(self):
        """Test is_high_half helper when IDA is not available."""
        from d810.optimizers.extensions import when

        # Without IDA, should return True (permissive for testing)
        ctx = {"_candidate": None}
        result = when.dst.is_high_half(ctx)
        assert result is True

    def test_is_register_without_ida(self):
        """Test is_register helper when IDA is not available."""
        from d810.optimizers.extensions import when

        # Without IDA, should return True (permissive for testing)
        ctx = {"_candidate": None}
        result = when.dst.is_register(ctx)
        assert result is True

    def test_is_memory_without_ida(self):
        """Test is_memory helper when IDA is not available."""
        from d810.optimizers.extensions import when

        # Without IDA, should return True (permissive for testing)
        ctx = {"_candidate": None}
        result = when.dst.is_memory(ctx)
        assert result is True


class TestContextProviders:
    """Test context providers for binding variables."""

    def test_parent_register_without_ida(self):
        """Test parent_register provider when IDA is not available."""
        from d810.optimizers.extensions import context

        # Without IDA, should return a mock AstLeaf
        ctx = {"_candidate": None}
        result = context.dst.parent_register(ctx)

        # Should return an AstLeaf even without IDA
        assert result is not None
        assert hasattr(result, 'name')
        assert result.name == "parent_reg"

    def test_operand_size_without_candidate(self):
        """Test operand_size provider when candidate is missing."""
        from d810.optimizers.extensions import context

        ctx = {}
        result = context.dst.operand_size(ctx)
        assert result is None


class TestContextAwareRule:
    """Test context-aware rule framework integration."""

    def test_rule_imports_correctly(self):
        """Test that the context-aware rule can be imported."""
        try:
            from d810.optimizers.microcode.instructions.pattern_matching.rewrite_mov_context_aware import (
                ReplaceMovHighContext,
            )

            # Verify the rule has the expected attributes
            assert hasattr(ReplaceMovHighContext, 'PATTERN')
            assert hasattr(ReplaceMovHighContext, 'REPLACEMENT')
            assert hasattr(ReplaceMovHighContext, 'CONSTRAINTS')
            assert hasattr(ReplaceMovHighContext, 'CONTEXT_VARS')
            assert hasattr(ReplaceMovHighContext, 'UPDATE_DESTINATION')

            # Verify class attributes are set correctly
            assert ReplaceMovHighContext.UPDATE_DESTINATION == "full_reg"
            assert "full_reg" in ReplaceMovHighContext.CONTEXT_VARS
            assert len(ReplaceMovHighContext.CONSTRAINTS) > 0

        except ImportError as e:
            pytest.skip(f"Could not import context-aware rule: {e}")

    def test_rule_instance_creation(self):
        """Test that we can create an instance of the context-aware rule."""
        try:
            from d810.optimizers.microcode.instructions.pattern_matching.rewrite_mov_context_aware import (
                ReplaceMovHighContext,
            )

            rule = ReplaceMovHighContext()

            # Check that the rule has the required properties
            assert rule.name == "ReplaceMovHighContext"
            assert rule.SKIP_VERIFICATION is True  # Size-changing rule
            assert hasattr(rule, 'check_candidate')

        except ImportError as e:
            pytest.skip(f"Could not import context-aware rule: {e}")

    def test_context_vars_processing(self):
        """Test that CONTEXT_VARS are processed correctly."""
        try:
            from d810.optimizers.microcode.instructions.pattern_matching.rewrite_mov_context_aware import (
                ReplaceMovHighContext,
            )

            rule = ReplaceMovHighContext()

            # Verify CONTEXT_VARS structure
            assert isinstance(rule.CONTEXT_VARS, dict)
            assert "full_reg" in rule.CONTEXT_VARS

            # The value should be a callable (the context provider)
            provider = rule.CONTEXT_VARS["full_reg"]
            assert callable(provider)

        except ImportError as e:
            pytest.skip(f"Could not import context-aware rule: {e}")


class TestContextAwareDSLDocumentation:
    """Test that the context-aware DSL has proper documentation."""

    def test_extensions_module_has_docstring(self):
        """Verify the extensions module has documentation."""
        from d810.optimizers import extensions

        assert extensions.__doc__ is not None
        assert "context-aware" in extensions.__doc__.lower()

    def test_helpers_have_docstrings(self):
        """Verify all helpers have documentation."""
        from d810.optimizers.extensions import DestinationHelpers, ContextProviders

        # Check DestinationHelpers
        assert DestinationHelpers.is_high_half.__doc__ is not None
        assert DestinationHelpers.is_register.__doc__ is not None
        assert DestinationHelpers.is_memory.__doc__ is not None

        # Check ContextProviders
        assert ContextProviders.parent_register.__doc__ is not None
        assert ContextProviders.operand_size.__doc__ is not None

    def test_example_rule_has_comprehensive_docstring(self):
        """Verify the example rule has comprehensive documentation."""
        try:
            from d810.optimizers.microcode.instructions.pattern_matching.rewrite_mov_context_aware import (
                ReplaceMovHighContext,
            )

            docstring = ReplaceMovHighContext.__doc__
            assert docstring is not None
            assert "when.dst.is_high_half" in docstring
            assert "context.dst.parent_register" in docstring
            assert "UPDATE_DESTINATION" in docstring
            assert "Example:" in docstring

        except ImportError as e:
            pytest.skip(f"Could not import context-aware rule: {e}")
