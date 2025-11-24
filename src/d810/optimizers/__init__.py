"""D810 optimizer infrastructure and refactored systems.

This module provides the foundational components for the d810 optimization system:
- Declarative DSL for pattern matching
- Core optimization base classes
- Instrumentation for tracking deobfuscation
- Caching for persistent optimization results
- Profiling for performance analysis
- Parallel execution for multi-core optimization
- Centralized optimization manager
"""

# Core infrastructure (must be imported first)
from . import rules

# Try to import IDA-dependent modules
try:
    from . import core
    from . import instrumentation
    from . import caching
    from . import profiling
    from . import parallel
    from . import manager
    IDA_AVAILABLE = True
except (ImportError, ModuleNotFoundError):
    # Allow module to be imported for unit testing without IDA Pro
    IDA_AVAILABLE = False
    core = None  # type: ignore
    instrumentation = None  # type: ignore
    caching = None  # type: ignore
    profiling = None  # type: ignore
    parallel = None  # type: ignore
    manager = None  # type: ignore

# Re-export commonly used classes for convenience
from d810.mba.dsl import Var, Const, DynamicConst, when
from .rules import VerifiableRule

if IDA_AVAILABLE:
    from .core import OptimizationContext, OptimizationRule
    from .instrumentation import DeobfuscationContext
    from .manager import OptimizerManager, create_default_manager

__all__ = [
    # Modules
    "core",
    "rules",
    "instrumentation",
    "caching",
    "profiling",
    "parallel",
    "manager",
    # Commonly used classes (re-exported for convenience)
    "Var",
    "Const",
    "DynamicConst",
    "when",
    "OptimizationContext",
    "OptimizationRule",
    "VerifiableRule",
    "DeobfuscationContext",
    "OptimizerManager",
    "create_default_manager",
]
