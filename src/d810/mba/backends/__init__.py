"""Backends for MBA expression processing.

This package contains different backend implementations for working with
MBA expressions:

- z3: Z3 SMT solver backend for verification and equivalence checking
- ida: IDA Pro integration (minsn_t ↔ SymbolicExpression conversion)
- egraph (future): E-graph backend for optimization via saturation

Each backend is optional and can be used independently based on available
dependencies and use case.
"""

__version__ = "0.1.0"

# Z3 backend (requires z3-solver)
try:
    from d810.mba.backends.z3 import (
        Z3_INSTALLED,
        get_solver,
        z3_prove_equivalence,
        ast_to_z3_expression,
        # Pure SymbolicExpression verification (no IDA needed)
        verify_rule,
    )
    __all__ = [
        "Z3_INSTALLED",
        "get_solver",
        "z3_prove_equivalence",
        "ast_to_z3_expression",
        "verify_rule",
    ]
except ImportError:
    Z3_INSTALLED = False
    __all__ = ["Z3_INSTALLED"]

# IDA backend (requires IDA Pro)
# These imports are lazy (inside functions) so won't fail without IDA
from d810.mba.backends.ida import (
    IDANodeVisitor,
    IDAPatternAdapter,
    adapt_rules,
)
__all__.extend([
    "IDANodeVisitor",
    "IDAPatternAdapter",
    "adapt_rules",
])

# Future: E-graph backend
# from d810.mba.backends.egraph import EGraphSimplifier
