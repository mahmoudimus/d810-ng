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
    )
    __all__ = [
        "Z3_INSTALLED",
        "get_solver",
        "z3_prove_equivalence",
        "ast_to_z3_expression",
    ]
except ImportError:
    Z3_INSTALLED = False
    __all__ = ["Z3_INSTALLED"]

# Future: E-graph backend
# from d810.mba.backends.egraph import EGraphSimplifier

# Future: IDA backend (for minsn_t conversion)
# from d810.mba.backends.ida import minsn_to_symbolic, symbolic_to_minsn
