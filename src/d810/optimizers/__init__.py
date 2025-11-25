"""D810 optimizer infrastructure and refactored systems.

This module provides the foundational components for the d810 optimization system:
- Declarative DSL for pattern matching
- Core optimization base classes
- Caching for persistent optimization results
- Centralized optimization manager
"""

# Try to import IDA-dependent modules
try:
    from . import core
    from . import caching
    from . import manager
    IDA_AVAILABLE = True
except (ImportError, ModuleNotFoundError):
    # Allow module to be imported for unit testing without IDA Pro
    IDA_AVAILABLE = False
    core = None  # type: ignore
    caching = None  # type: ignore
    manager = None  # type: ignore

# Re-export commonly used classes for convenience
from d810.mba.dsl import Var, Const, DynamicConst, when
from d810.mba.rules import VerifiableRule

if IDA_AVAILABLE:
    from .core import OptimizationContext, OptimizationRule
    from .manager import OptimizerManager, create_default_manager

__all__ = [
    # Modules
    "core",
    "caching",
    "manager",
    # Commonly used classes (re-exported for convenience)
    "Var",
    "Const",
    "DynamicConst",
    "when",
    "OptimizationContext",
    "OptimizationRule",
    "VerifiableRule",
    "OptimizerManager",
    "create_default_manager",
]
