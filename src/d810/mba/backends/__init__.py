"""Backends for MBA expression processing.

This package contains different backend implementations for working with
MBA expressions (d810.mba.dsl.SymbolicExpression):

- z3: Z3 SMT solver backend for verification and equivalence checking
- ida: IDA Pro integration (minsn_t ↔ SymbolicExpression conversion)
- egraph (future): E-graph backend for optimization via saturation

Each backend is optional and can be used independently based on available
dependencies and use case.

=============================================================================
IMPORTANT: Z3 Module Separation
=============================================================================

There are TWO Z3 modules in d810 - do NOT confuse them:

1. d810.mba.backends.z3 (THIS PACKAGE - pure, no IDA)
   - Works with: SymbolicExpression (platform-independent)
   - Use for: Unit tests, CI, TDD, mathematical verification
   - Exports: Z3VerificationVisitor, prove_equivalence, verify_rule

2. d810.expr.z3_utils (SEPARATE - IDA-specific)
   - Works with: AstNode, mop_t, minsn_t (IDA types)
   - Use for: Runtime verification inside IDA Pro plugin
   - Exports: ast_to_z3_expression, z3_check_mop_equality

See the module docstrings in each file for full details.
=============================================================================
"""

__version__ = "0.1.0"

# Z3 backend (requires z3-solver)
try:
    from d810.mba.backends.z3 import (  # VerificationEngine implementation; Pure SymbolicExpression verification (no IDA needed); Z3 variable creation; Constraint conversion (ConstraintExpr → Z3)
        Z3_INSTALLED,
        Z3VerificationEngine,
        Z3VerificationVisitor,
        constraint_to_z3,
        create_z3_variables,
        prove_equivalence,
        verify_rule,
    )

    __all__ = [
        "Z3_INSTALLED",
        "Z3VerificationEngine",
        "Z3VerificationVisitor",
        "prove_equivalence",
        "verify_rule",
        "create_z3_variables",
        "constraint_to_z3",
    ]
except ImportError:
    Z3_INSTALLED = False
    __all__ = ["Z3_INSTALLED"]
else:
    Z3_AVAILABLE = True
    __all__.extend(
        [
            "Z3_AVAILABLE",
        ]
    )


try:
    # IDA backend (requires IDA Pro)
    # These imports are lazy (inside functions) so won't fail without IDA
    from d810.mba.backends.ida import IDANodeVisitor, IDAPatternAdapter, adapt_rules
except ImportError:
    IDA_AVAILABLE = False
    __all__.extend(
        [
            "IDA_AVAILABLE",
        ]
    )
else:
    IDA_AVAILABLE = True
    __all__.extend(
        [
            "IDA_AVAILABLE",
            "IDANodeVisitor",
            "IDAPatternAdapter",
            "adapt_rules",
        ]
    )

# Future: E-graph backend
# from d810.mba.backends.egraph import EGraphSimplifier
