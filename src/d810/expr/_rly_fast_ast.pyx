# distutils: language = c++
# cython: language_level=3, embedsignature=True
# distutils: define_macros=__EA64__=1

from cython.operator cimport dereference as deref
from libcpp.memory cimport unique_ptr
from libcpp.utility cimport move
from cpython.ref cimport PyObject
from libcpp.unordered_map cimport unordered_map

import ida_hexrays

from d810.conf.loggers import getLogger
import d810.hexrays.hexrays_formatters as fmt
from d810.cythxr._chexrays cimport (
    ea_t,
    mcode_t,
    minsn_t,
    mop_t_ptr,
    mop_t,
    mopt_t,
    MOPT,
    qstring,
    qvector,
    SwigPyObject,
    SwigPyObject,
    SwigPyObjectPtr,
    swigtocpp,
    uint64,
)

logger = getLogger(__name__)

# C++ struct definition
cdef extern from *:
    """
    namespace d810 {
    struct TempAstNode {
        mcode_t opcode;
        TempAstNode* left;
        TempAstNode* right;
        TempAstNode* dst;
        bool is_leaf;
        bool is_const;
        PyObject* py_mop;  // Use PyObject* for proper refcounting

        int ast_index;
        int dest_size;
        ea_t ea;

        TempAstNode()
          : opcode(m_nop),
            left(nullptr), right(nullptr), dst(nullptr),
            is_leaf(false), is_const(false),
            py_mop(nullptr),
            ast_index(-1), dest_size(0), ea(0) {}

        ~TempAstNode() {
            Py_XDECREF(py_mop);
        }

        void set_py_mop(PyObject* obj) {
            Py_XINCREF(obj);
            Py_XDECREF(py_mop);
            py_mop = obj;
        }
    };
    } // namespace d810
    """
    pass

# C++ class declaration for Cython
cdef extern from * namespace "d810":
    cdef cppclass TempAstNode:
        mcode_t opcode
        TempAstNode* left
        TempAstNode* right
        TempAstNode* dst
        bint is_leaf
        bint is_const
        PyObject* py_mop
        int ast_index
        int dest_size
        ea_t ea

        TempAstNode() except +
        void set_py_mop(PyObject* obj)


ctypedef TempAstNode* TempAstNodePtr
ctypedef unordered_map[qstring, TempAstNodePtr] qstr2node_map
ctypedef qvector[TempAstNodePtr] node_vec

cdef class AstBuildContext:
    cdef:
        qvector[unique_ptr[TempAstNode]] node_pool
        qstr2node_map mop_key_to_node
        node_vec unique_nodes
        size_t pool_size
        object mba_opcodes

    def __cinit__(self, object mba_opcodes, size_t pool_size=1024): # type: ignore
        self.mba_opcodes = mba_opcodes
        self.pool_size = pool_size
        self.node_pool.reserve(pool_size) # type: ignore
        self.reset()

    def __dealloc__(self):
        # RAII: node_pool will be cleared by the destructor of unique_ptr
        self.node_pool.clear()
        self.mop_key_to_node.clear()
        self.unique_nodes.clear()

    cdef TempAstNodePtr new_node(self):
        cdef:
            # 1. Create a new node on the heap, wrapped in a unique_ptr
            unique_ptr[TempAstNode] node_ptr = unique_ptr[TempAstNode](new TempAstNode()) # type: ignore
            # 2. Get the raw pointer to return and use for inter-node links
            TempAstNodePtr raw_node_ptr = node_ptr.get()

        self.node_pool.push_back_move(move(node_ptr)) # type: ignore

        # The default constructor for TempAstNode already initialized it.
        return raw_node_ptr

    cdef void reset(self):
        # Clearing the pool in __dealloc__ is enough.
        # For a reset during lifetime, you'd clear and reserve again.
        self.node_pool.clear()
        self.node_pool.reserve(self.pool_size) # type: ignore
        self.mop_key_to_node.clear()
        self.unique_nodes.clear()
        self.mba_opcodes = None

# --------------------------
# Key helpers
# --------------------------

cdef qstring _mop_key(mop_t* mop):
    cdef:
        qstring key
        mopt_t t = mop.t

    # t, size, valnum header
    if t != MOPT.NUMBER:
        key.sprnt("%d,%d,", t, mop.size)
    else:
        key.sprnt("%d,%d,%d,", t, mop.size, mop.valnum)

    if t == MOPT.NUMBER:
        key.cat_sprnt("%llx", mop.nnn.value)
    elif t == MOPT.REGISTER:
        key.cat_sprnt("%d", mop.r)
    elif t == MOPT.DEST_RESULT and mop.d:
        # instruction string as identity
        key.cat_sprnt("%s", mop.d.dstr())
    elif t == MOPT.STACK:
        key.cat_sprnt("%llx", mop.s.off)
    elif t == MOPT.GLOBAL:
        key.cat_sprnt("%llx", <ea_t>mop.g)  # ea_t
    elif t == MOPT.LOCAL:
        key.cat_sprnt("%d,%lld", mop.l.idx, mop.l.off)
    elif t == MOPT.MBLOCK:
        key.cat_sprnt("%d", mop.b)
    elif t == MOPT.HELPER:
        key.cat_sprnt("%s", mop.helper)
    elif t == MOPT.STRING:
        key.cat_sprnt("%s", mop.cstr)
    else:
        key.cat_sprnt("%s", mop.dstr())
    return key

cdef qstring _ins_key(minsn_t* ins):
    # A simple, stable cache key: text form of instruction
    return qstring(ins.dstr())

# --------------------------
# Recursive builders
# --------------------------

cdef TempAstNodePtr _build_from_mop(AstBuildContext ctx, mop_t* mop):
    cdef:
        qstring key
        qstr2node_map.iterator it
        TempAstNodePtr node
        bint is_mba
        object new_mop_obj
        mop_t_ptr new_mop_obj_swig

    key = _mop_key(mop)
    it = ctx.mop_key_to_node.find(key)

    if it != ctx.mop_key_to_node.end():
        if logger.debug_on:
            # Avoid calling dstr() from Cython; just log type/size.
            try:
                logger.debug(
                    "[fast_ast] Reusing cached node for mop t=%d size=%d",
                    <int>mop.t,
                    <int>mop.size,
                )
            except Exception:
                pass
        return deref(it).second

    node = ctx.new_node()
    node.ast_index = ctx.unique_nodes.size()
    ctx.unique_nodes.push_back(node)

    # NB: don't rely on mop.ea (not always meaningful); leave 0 here.
    node.dest_size = mop.size

    if mop.t == MOPT.DEST_RESULT and mop.d:
        # Only build structured nodes for MBA-related opcodes, otherwise
        # treat the whole expression as a leaf (matches Python builder).
        is_mba = <bint>False
        if ctx.mba_opcodes is not None:
            try:
                # Cast to int to avoid Python int(mcode_t) issues in Cython
                is_mba = (<int>mop.d.opcode) in ctx.mba_opcodes
            except Exception:
                is_mba = <bint>False

        if is_mba:
            node.is_leaf = <bint>False
            node.opcode  = mop.d.opcode
            node.left  = _build_from_mop(ctx, &mop.d.l)
            node.right = _build_from_mop(ctx, &mop.d.r)
            node.dst   = _build_from_mop(ctx, &mop.d.d)
            if logger.debug_on:
                try:
                    logger.debug(
                        "[fast_ast] Building structured node opcode=%s size=%d",
                        fmt.opcode_to_string(<int>node.opcode),
                        <int>node.dest_size,
                    )
                except Exception:
                    pass
            new_mop_obj = ida_hexrays.mop_t()
            new_mop_obj_swig = swigtocpp[mop_t_ptr](<PyObject *>(new_mop_obj.this))
            new_mop_obj_swig.assign(deref(mop))
            node.set_py_mop(<PyObject*>new_mop_obj)
            # best-effort size if missing
            if node.dest_size == 0:
                if mop.d.d.size != 0:
                    node.dest_size = mop.d.d.size
                elif mop.d.l.size != 0:
                    node.dest_size = mop.d.l.size
            if logger.debug_on:
                try:
                    logger.debug(
                        "[fast_ast] Structured node finalized opcode=%s dest_size=%d",
                        fmt.opcode_to_string(<int>node.opcode),
                        <int>node.dest_size,
                    )
                except Exception:
                    pass
        else:
            node.is_leaf  = <bint>True
            node.is_const = <bint>(mop.t == MOPT.NUMBER)
            # node.pmop = make_shared[mop_t](deref(mop)) # type: ignore
            # --- FIX: Safely store a Python-managed copy of the leaf mop ---
            new_mop_obj = ida_hexrays.mop_t()
            new_mop_obj_swig = swigtocpp[mop_t_ptr](<PyObject *>(new_mop_obj.this))
            new_mop_obj_swig.assign(deref(mop))
            node.set_py_mop(<PyObject*>new_mop_obj)
            if logger.debug_on:
                try:
                    logger.debug(
                        "[fast_ast] Treating DEST_RESULT as leaf (non-MBA): %s",
                        fmt.format_mop_t(new_mop_obj),
                    )
                except Exception:
                    pass
    else:
        node.is_leaf  = <bint>True
        node.is_const = <bint>(mop.t == MOPT.NUMBER)
        #node.pmop = make_shared[mop_t](deref(mop)) # type: ignore
        new_mop_obj = ida_hexrays.mop_t()
        new_mop_obj_swig = swigtocpp[mop_t_ptr](<PyObject *>(new_mop_obj.this))
        new_mop_obj_swig.assign(deref(mop))
        node.set_py_mop(<PyObject*>new_mop_obj)
        if logger.debug_on:
            try:
                logger.debug(
                    "[fast_ast] Leaf node: %s",
                    fmt.format_mop_t(new_mop_obj),
                )
            except Exception:
                pass
    ctx.mop_key_to_node[key] = node
    return node

cdef TempAstNodePtr _build_from_ins(AstBuildContext ctx, minsn_t* ins):
    # Build directly from the instruction; no temporary mop_t.
    cdef TempAstNodePtr root = ctx.new_node()
    if root == NULL:
        return NULL

    root.is_leaf = <bint>False
    root.opcode  = ins.opcode
    # best-effort size if missing
    root.dest_size = ins.d.size if ins.d.size != 0 else ins.l.size

    # Recurse on operands
    root.left  = _build_from_mop(ctx, &ins.l)
    root.right = _build_from_mop(ctx, &ins.r)
    root.dst   = _build_from_mop(ctx, &ins.d)

    root.ea = ins.ea
    if logger.debug_on:
        try:
            logger.debug(
                "[fast_ast] Built instruction root opcode=%d ea=0x%x dest_size=%d",
                <int>root.opcode,
                <uint64>root.ea,
                <int>root.dest_size,
            )
        except Exception:
            pass
    return root


cdef object _to_py(TempAstNodePtr n,
                   object AstNode,
                   object AstLeaf,
                   object AstConstant,
                   object get_constant_mop):
    cdef:
        uint64 v
        object py
        str hex_v
        int size
        object mop_obj

    if not n:
        return None

    if not n.py_mop:
        mop_obj = None
    else:
        mop_obj = <object>(n.py_mop)
    if n.is_leaf:
        if n.is_const:
            # v = n.pmop.get().nnn.value
            v = mop_obj.nnn.value
            size = mop_obj.size
            hex_v = hex(v)
            py = AstConstant(hex_v, v, size)
            # only constants get a Python mop, via provided callback
            py.mop = get_constant_mop(v, size)
        else:
            # non-const leaf: just give it a readable label
            py = AstLeaf(mop_obj.dstr())
            py.mop = mop_obj
            # py.mop = mop_t()
            # py.mop.assign(deref(n.pmop.get()))
    else:
        py = AstNode(
            n.opcode,
            _to_py(n.left,  AstNode, AstLeaf, AstConstant, get_constant_mop),
            _to_py(n.right, AstNode, AstLeaf, AstConstant, get_constant_mop),
            _to_py(n.dst,   AstNode, AstLeaf, AstConstant, get_constant_mop),
        )
        py.mop = mop_obj

    py.dest_size = n.dest_size
    py.ea        = n.ea
    py.ast_index = n.ast_index
    return py

# --------------------------
# Public entry
# --------------------------

cpdef object fast_minsn_to_ast(object ins_py,
                               object MOP_TO_AST_CACHE,
                               object AstProxy,
                               object AstNode,
                               object AstLeaf,
                               object AstConstant,
                               object get_constant_mop,
                               object MBA_RELATED_OPCODES):
    cdef:
        SwigPyObject* swig_obj
        minsn_t* ins
        qstring qk
        bytes key
        object tmpl
        AstBuildContext ctx
        TempAstNodePtr root
        object py_tmpl


    swig_obj = swigtocpp[SwigPyObjectPtr](<PyObject *>(ins_py.this))

    ins = <minsn_t*>swig_obj.ptr

    if ins == NULL:
        if logger.debug_on:
            try:
                logger.debug(
                    "[fast_ast] Null instruction pointer; py=%s",
                    fmt.format_minsn_t(<object>ins_py),
                )
            except Exception:
                pass
        return None

    # very light filter: only real ops or instruction results
    if ins.opcode == mcode_t.m_nop:
        if logger.debug_on:
            try:
                logger.debug(
                    "[fast_ast] Skipping m_nop: %s",
                    fmt.format_minsn_t(<object>ins_py),
                )
            except Exception:
                pass
        return None

    # cache
    qk = _ins_key(ins)
    key = qk.c_str()
    if key in MOP_TO_AST_CACHE:
        tmpl = MOP_TO_AST_CACHE[key]
        if logger.debug_on:
            try:
                logger.debug(
                    "[fast_ast] Cache hit: %s",
                    fmt.format_minsn_t(<object>ins_py),
                )
            except Exception:
                pass
        return None if tmpl is None else AstProxy(tmpl)

    ctx = AstBuildContext(MBA_RELATED_OPCODES)
    root = _build_from_ins(ctx, ins)
    if root == NULL:
        MOP_TO_AST_CACHE[key] = None
        if logger.debug_on:
            try:
                logger.debug(
                    "[fast_ast] Failed to build AST root; caching miss: %s",
                    fmt.format_minsn_t(<object>ins_py),
                )
            except Exception:
                pass
        return None

    py_tmpl = _to_py(root, AstNode, AstLeaf, AstConstant, get_constant_mop)
    if py_tmpl is None:
        MOP_TO_AST_CACHE[key] = None
        if logger.debug_on:
            try:
                logger.debug(
                    "[fast_ast] _to_py returned None; caching miss: %s",
                    fmt.format_minsn_t(<object>ins_py),
                )
            except Exception:
                pass
        return None

    # let your Python side finalize the template
    if hasattr(py_tmpl, "compute_sub_ast"):
        py_tmpl.compute_sub_ast()
    if hasattr(py_tmpl, "freeze"):
        py_tmpl.freeze()

    MOP_TO_AST_CACHE[key] = py_tmpl
    if logger.debug_on:
        try:
            logger.debug(
                "[fast_ast] Cached AST template: %s (opcode=%s)",
                fmt.format_minsn_t(<object>ins_py),
                fmt.opcode_to_string(getattr(<object>ins_py, "opcode", -1)),
            )
        except Exception:
            pass
    return AstProxy(py_tmpl)
