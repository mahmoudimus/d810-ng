

cdef class AstBase:
    cdef public dict sub_ast_info_by_index
    cdef public object mop
    cdef public object dst_mop
    cdef public object dest_size
    cdef public object ea
    cdef public object ast_index

cdef class AstNode(AstBase):
    cdef public object opcode
    cdef public object left
    cdef public object right
    cdef public object dst
    cdef public object dst_mop
    cdef public list opcodes
    cdef public bint is_candidate_ok
    cdef public list leafs
    cdef public dict leafs_by_name
    cdef public object func_name
    cdef public bint _is_frozen

cdef class AstLeaf(AstBase):
    cdef public object name
    cdef public object z3_var
    cdef public object z3_var_name
    cdef public bint _is_frozen

cdef class AstConstant(AstLeaf):
    cdef public object expected_value
    cdef public object expected_size