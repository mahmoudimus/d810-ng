from d810.cythxr.cymode import CythonMode

if CythonMode().is_enabled():
    from d810.expr._ast import (
        AstBase,
        AstConstant,
        AstLeaf,
        AstNode,
        AstProxy,
        minsn_to_ast,
        mop_to_ast,
    )
else:
    from d810.expr._slow_ast import (
        AstBase,
        AstConstant,
        AstLeaf,
        AstNode,
        AstProxy,
        minsn_to_ast,
        mop_to_ast,
    )
