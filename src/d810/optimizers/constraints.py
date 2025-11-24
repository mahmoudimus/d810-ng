"""Backward compatibility re-export of d810.mba.constraints.

This module provides backward compatibility for code that imports from
d810.optimizers.constraints. The canonical implementation is now in
d810.mba.constraints (pure Python, no IDA dependencies).

All exports are re-exported from d810.mba.constraints to avoid code duplication.
"""

# Re-export everything from the canonical location
from d810.mba.constraints import (
    ConstraintExpr,
    EqualityConstraint,
    ComparisonConstraint,
    AndConstraint,
    OrConstraint,
    NotConstraint,
    is_constraint_expr,
)

__all__ = [
    "ConstraintExpr",
    "EqualityConstraint",
    "ComparisonConstraint",
    "AndConstraint",
    "OrConstraint",
    "NotConstraint",
    "is_constraint_expr",
]
