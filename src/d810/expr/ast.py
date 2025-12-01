"""AST module dispatcher - uses Cython speedups if available, otherwise pure Python."""

from d810.core.cymode import CythonMode

# Try to import Cython-optimized version first, respecting CythonMode
if CythonMode().is_enabled():
    try:
        from d810.speedups.expr.c_ast import (
            AstBase,
            AstConstant,
            AstLeaf,
            AstNode,
            AstProxy,
            get_constant_mop,
            minsn_to_ast,
            mop_to_ast,
        )

        _USING_CYTHON = True
    except (ModuleNotFoundError, ImportError):
        # Fall back to pure Python implementation
        from d810.expr.p_ast import (
            AstBase,
            AstConstant,
            AstLeaf,
            AstNode,
            AstProxy,
            get_constant_mop,
            minsn_to_ast,
            mop_to_ast,
        )

        _USING_CYTHON = False
else:
    # CythonMode disabled, use pure Python
    from d810.expr.p_ast import (
        AstBase,
        AstConstant,
        AstLeaf,
        AstNode,
        AstProxy,
        get_constant_mop,
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
    "get_constant_mop",
    "minsn_to_ast",
    "mop_to_ast",
]
