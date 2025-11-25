"""Basic tests for the OptimizationRule class using pytest style."""

import ida_hexrays

from d810.optimizers.microcode.handler import OptimizationRule


def test_name_and_description_defaults():
    """Test default name and description."""
    rule = OptimizationRule()
    # Default name comes from class name
    assert rule.name == "OptimizationRule"
    # No DESCRIPTION set => fallback message
    assert rule.description == "No description available"


def test_set_log_dir():
    """Test setting log directory."""
    rule = OptimizationRule()
    rule.set_log_dir("/tmp/logs")
    assert rule.log_dir == "/tmp/logs"


def test_configure_none():
    """Test configure with None."""
    rule = OptimizationRule()
    rule.configure(None)
    # No maturities => default empty
    assert rule.config == {}
    assert rule.maturities == []


def test_configure_empty_dict():
    """Test configure with empty dict."""
    rule = OptimizationRule()
    rule.configure({})
    assert rule.config == {}
    assert rule.maturities == []


def test_configure_with_maturities():
    """Test configure with maturities."""
    rule = OptimizationRule()
    config = {"maturities": ["LOCOPT", "CALLS"]}
    rule.configure(config)
    # Config stored
    assert rule.config == config
    # Maturities converted to Hex-Rays constants
    expected = [ida_hexrays.MMAT_LOCOPT, ida_hexrays.MMAT_CALLS]
    assert rule.maturities == expected
