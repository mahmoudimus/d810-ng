"""AST module dispatcher - uses Cython speedups if available, otherwise pure Python."""

# Try to import Cython-optimized version first
try:
    from speedups.expr.ast import (
        AstBase,
        AstConstant,
        AstLeaf,
        AstNode,
        AstProxy,
        minsn_to_ast,
        mop_to_ast,
    )
    _USING_CYTHON = True
except ImportError:
    # Fall back to pure Python implementation
    from d810.expr._slow_ast import (
        AstBase,
        AstConstant,
        AstLeaf,
        AstNode,
        AstProxy,
        minsn_to_ast,
        mop_to_ast,
    )
    _USING_CYTHON = False

__all__ = [
    "AstBase",
    "AstConstant",
    "AstLeaf",
    "AstNode",
    "AstProxy",
    "minsn_to_ast",
    "mop_to_ast",
]
