"""d810.mba - Mixed Boolean Arithmetic verification and simplification.

This package provides IDA-independent tools for:
- Symbolic expression DSL
- Constraint system
- Z3-based theorem proving
- MBA simplification algorithms

The package is designed to be reusable outside of d810/IDA Pro.
"""

__version__ = "0.1.0"

# Phase 2 & 3 complete: Pure Python components and verifier available
from d810.core.bits import SUB_TABLE, AND_TABLE
from d810.mba.dsl import (
    Var,
    Const,
    Zext,
    SymbolicExpression,
)
from d810.mba.constraints import (
    ConstraintExpr,
    EqualityConstraint,
    ComparisonConstraint,
    AndConstraint,
    OrConstraint,
    NotConstraint,
)
from d810.mba.visitors import (
    Z3VerificationVisitor,
    prove_equivalence,
)
from d810.mba.verifier import (
    MBARule,
    ConstrainedMBARule,
    verify_transformation,
)
from d810.mba.rules import (
    RuleRegistry,
    SymbolicRule,
    VerifiableRule,
    RULE_REGISTRY,
)

# Public API
__all__ = [
    # Constants
    "SUB_TABLE",
    "AND_TABLE",

    # DSL
    "Var",
    "Const",
    "Zext",
    "SymbolicExpression",

    # Constraints
    "ConstraintExpr",
    "EqualityConstraint",
    "ComparisonConstraint",
    "AndConstraint",
    "OrConstraint",
    "NotConstraint",

    # Z3 backend
    "Z3VerificationVisitor",
    "prove_equivalence",

    # Verifier (Phase 3)
    "MBARule",
    "ConstrainedMBARule",
    "verify_transformation",

    # Rules
    "RuleRegistry",
    "SymbolicRule",
    "VerifiableRule",
    "RULE_REGISTRY",
]
