"""d810.mba - Mixed Boolean Arithmetic verification and simplification.

This package provides IDA-independent tools for:
- Symbolic expression DSL
- Constraint system
- Z3-based theorem proving
- MBA simplification algorithms

The package is designed to be reusable outside of d810/IDA Pro.
"""

__version__ = "0.1.0"

# Public API - available after MBA separation is complete
__all__ = [
    # DSL will be exported here after Phase 2
    # "Var", "Const", "Zext", "SymbolicExpression",

    # Constraints will be exported after Phase 2
    # "ConstraintExpr",

    # Z3 backend will be exported after Phase 2
    # "prove_equivalence",

    # Verifier will be exported after Phase 3
    # "MBARule", "verify_transformation",
]
