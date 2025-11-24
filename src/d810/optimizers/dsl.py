"""Backward compatibility re-export of d810.mba.dsl.

This module provides backward compatibility for code that imports from
d810.optimizers.dsl. The canonical implementation is now in d810.mba.dsl
(pure Python, no IDA dependencies).

All exports are re-exported from d810.mba.dsl to avoid code duplication.
"""

# Re-export everything from the canonical location
from d810.mba.dsl import (
    SymbolicExpression,
    Var,
    Const,
    Zext,
    DynamicConst,
    ConstraintPredicate,
)

__all__ = [
    "SymbolicExpression",
    "Var",
    "Const",
    "Zext",
    "DynamicConst",
    "ConstraintPredicate",
]
