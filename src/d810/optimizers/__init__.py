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
from . import dsl
from . import core
from . import rules

# Advanced features
from . import instrumentation
from . import caching
from . import profiling
from . import parallel
from . import manager

# Re-export commonly used classes for convenience
from .dsl import Var, Const, DynamicConst, when
from .core import OptimizationContext, OptimizationRule
from .rules import VerifiableRule
from .instrumentation import DeobfuscationContext
from .manager import OptimizerManager, create_default_manager

__all__ = [
    # Modules
    "dsl",
    "core",
    "rules",
    "instrumentation",
    "caching",
    "profiling",
    "parallel",
    "manager",
    # Commonly used classes
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
