"""IDA-specific Z3 utilities for microcode verification.

This module provides Z3 verification for IDA Pro microcode (AstNode, mop_t, minsn_t).
It is used at RUNTIME during deobfuscation to verify transformations are correct.

=============================================================================
ARCHITECTURE: Two Z3 Modules in d810
=============================================================================

There are TWO separate Z3 utility modules in d810, serving different purposes:

1. d810.mba.backends.z3 (PURE - no IDA)
   --------------------------------------
   Purpose: Verify optimization rules using pure symbolic expressions.
   Input:   d810.mba.dsl.SymbolicExpression (platform-independent DSL)
   Use:     Unit tests, CI, TDD rule development, mathematical verification

   Key exports:
   - Z3VerificationVisitor: Converts SymbolicExpression → Z3 BitVec
   - prove_equivalence(): Prove two SymbolicExpressions are equivalent
   - verify_rule(): Verify a rule's PATTERN equals its REPLACEMENT

2. THIS FILE: d810.expr.z3_utils (IDA-SPECIFIC)
   ---------------------------------------------
   Purpose: Z3 verification of actual IDA microcode during deobfuscation.
   Input:   d810.expr.ast.AstNode (wraps IDA mop_t/minsn_t)
   Use:     Runtime verification inside IDA Pro plugin

   Key exports:
   - ast_to_z3_expression(): Converts AstNode → Z3 BitVec
   - z3_check_mop_equality(): Check if two mop_t are semantically equivalent
   - z3_check_mop_inequality(): Check if two mop_t are NOT equivalent
   - log_z3_instructions(): Debug logging for Z3 verification

=============================================================================
WHY TWO MODULES?
=============================================================================

The separation enables:
1. Unit testing rules WITHOUT IDA Pro license
2. CI/CD pipeline verification (GitHub Actions)
3. TDD workflow: write rule → verify with Z3 → integrate with IDA
4. Clear dependency boundaries (mba/ never imports IDA modules)

If you need to verify a SymbolicExpression (from d810.mba.dsl), use:
    from d810.mba.backends.z3 import prove_equivalence

If you need to verify actual IDA microcode (AstNode/mop_t), use this module:
    from d810.expr.z3_utils import z3_check_mop_equality

=============================================================================
TODO: Refactor to Visitor Pattern
=============================================================================

This module is technical debt. It uses procedural functions (ast_to_z3_expression,
z3_prove_equivalence, etc.) instead of a clean visitor pattern like
Z3VerificationVisitor in mba/backends/z3.py.

The ideal architecture would be:

    class AstNodeZ3Visitor:
        '''Visitor that converts AstNode to Z3 for IDA microcode verification.'''
        def visit(self, node: AstNode) -> z3.BitVecRef: ...

This would:
1. Mirror the clean design of Z3VerificationVisitor
2. Make the code more maintainable and testable
3. Allow easier extension for new opcodes
4. Consolidate the scattered ast_to_z3_expression logic

Low priority since this code works and is only used at runtime inside IDA.
=============================================================================
"""

import functools
import typing
from typing import Dict, Tuple

# Check if IDA is available
try:
    import ida_hexrays
    IDA_AVAILABLE = True
except ImportError:
    IDA_AVAILABLE = False
    # Mock IDA types for function signatures only
    class _MockIDAHexrays:  # type: ignore
        class mop_t:
            pass
        class minsn_t:
            pass
    ida_hexrays = _MockIDAHexrays()

from d810.core import getLogger
from d810.errors import D810Z3Exception
from d810.expr.ast import AstLeaf, AstNode, minsn_to_ast, mop_to_ast
from d810.hexrays.hexrays_formatters import (
    format_minsn_t,
    format_mop_t,
    opcode_to_string,
)
from d810.hexrays.hexrays_helpers import get_mop_index, structural_mop_hash

logger = getLogger(__name__)
z3_file_logger = getLogger("D810.z3_test")

try:
    import z3

    Z3_INSTALLED = True
    # Since version 4.8.2, when Z3 is creating a BitVec, it relies on _str_to_bytes which uses sys.stdout.encoding
    # However, in IDA Pro (7.6sp1) sys.stdout is an object of type IDAPythonStdOut
    # which doesn't have a 'encoding' attribute, thus we set it to something, so that Z3 works
    import sys

    try:
        x = sys.stdout.encoding
    except AttributeError:
        logger.debug("Couldn't find sys.stdout.encoding, setting it to utf-8")
        sys.stdout.encoding = "utf-8"  # type: ignore
except ImportError:
    logger.info("Z3 features disabled. Install Z3 to enable them")
    Z3_INSTALLED = False


@functools.lru_cache(maxsize=1)
def requires_z3_installed(func: typing.Callable[..., typing.Any]):
    @functools.wraps(func)
    def wrapper(*args, **kwargs):
        if not Z3_INSTALLED:
            raise D810Z3Exception("Z3 is not installed")
        return func(*args, **kwargs)

    return wrapper


@requires_z3_installed
@functools.lru_cache(maxsize=1)
def get_solver() -> z3.Solver:
    s = z3.Solver()
    # Bound solver work to prevent pathological slowdowns in hot paths.
    # 50ms per query is generally enough for our simple equalities and keeps
    # total time bounded in large functions.
    try:
        p = z3.ParamsRef()
        p.set("timeout", 50)  # milliseconds
        s.set(params=p)
    except Exception:
        # Older z3 versions or API quirks – ignore and keep default settings.
        pass
    return s


@requires_z3_installed
def create_z3_vars(leaf_list: list[AstLeaf]):
    known_leaf_list = []
    known_leaf_z3_var_list = []
    for leaf in leaf_list:
        if leaf.is_constant() or leaf.mop is None:
            continue
        leaf_index = get_mop_index(leaf.mop, known_leaf_list)
        if leaf_index == -1:
            known_leaf_list.append(leaf.mop)
            leaf_index = len(known_leaf_list) - 1
            if leaf.mop.size in [1, 2, 4, 8]:
                # Normally, we should create variable based on their size
                # but for now it can cause issue when instructions like XDU are used, hence this ugly fix
                # known_leaf_z3_var_list.append(z3.BitVec("x_{0}".format(leaf_index), 8 * leaf.mop.size))
                known_leaf_z3_var_list.append(z3.BitVec("x_{0}".format(leaf_index), 32))
                pass
            else:
                known_leaf_z3_var_list.append(z3.BitVec("x_{0}".format(leaf_index), 32))
        leaf.z3_var = known_leaf_z3_var_list[leaf_index]
        leaf.z3_var_name = "x_{0}".format(leaf_index)
    return known_leaf_z3_var_list


@requires_z3_installed
def ast_to_z3_expression(ast: AstNode | AstLeaf | None, use_bitvecval=False):
    if ast is None:
        raise ValueError("ast is None")

    if ast.is_leaf():
        ast = typing.cast(AstLeaf, ast)
        if ast.is_constant():
            # Check if this is a pattern-matching constant with z3_var assigned
            # (e.g., Const("c_1") without concrete value)
            if hasattr(ast, 'z3_var') and ast.z3_var is not None:
                return ast.z3_var  # Use symbolic Z3 variable
            # Concrete constant (e.g., Const("ONE", 1))
            return z3.BitVecVal(ast.value, 32)
        return ast.z3_var

    ast = typing.cast(AstNode, ast)
    left = ast_to_z3_expression(ast.left, use_bitvecval)
    right = ast_to_z3_expression(ast.right, use_bitvecval) if ast.right else None

    match ast.opcode:
        case ida_hexrays.m_neg:
            return -left
        case ida_hexrays.m_lnot:
            # Logical NOT (!) returns 1 when the operand is zero, otherwise 0.
            # Implemented via a 32-bit conditional expression to avoid casting the
            # symbolic BitVec to a Python bool (which would raise a Z3 exception).
            return z3.If(
                left == z3.BitVecVal(0, 32),
                z3.BitVecVal(1, 32),
                z3.BitVecVal(0, 32),
            )
        case ida_hexrays.m_bnot:
            return ~left
        case ida_hexrays.m_add:
            return left + right
        case ida_hexrays.m_sub:
            return left - right
        case ida_hexrays.m_mul:
            return left * right
        case ida_hexrays.m_udiv:
            return z3.UDiv(
                ast_to_z3_expression(ast.left, use_bitvecval=True),
                ast_to_z3_expression(ast.right, use_bitvecval=True),
            )
        case ida_hexrays.m_sdiv:
            return left / right
        case ida_hexrays.m_umod:
            return z3.URem(left, right)
        case ida_hexrays.m_smod:
            return left % right
        case ida_hexrays.m_or:
            return left | right
        case ida_hexrays.m_and:
            return left & right
        case ida_hexrays.m_xor:
            return left ^ right
        case ida_hexrays.m_shl:
            return left << right
        case ida_hexrays.m_shr:
            return z3.LShR(left, right)
        case ida_hexrays.m_sar:
            return left >> right
        case ida_hexrays.m_setnz:
            return z3.If(
                left != z3.BitVecVal(0, 32), z3.BitVecVal(1, 32), z3.BitVecVal(0, 32)
            )
        case ida_hexrays.m_setz:
            return z3.If(
                left == z3.BitVecVal(0, 32), z3.BitVecVal(1, 32), z3.BitVecVal(0, 32)
            )
        case ida_hexrays.m_setae:
            return z3.If(z3.UGE(left, right), z3.BitVecVal(1, 32), z3.BitVecVal(0, 32))
        case ida_hexrays.m_setb:
            return z3.If(z3.ULT(left, right), z3.BitVecVal(1, 32), z3.BitVecVal(0, 32))
        case ida_hexrays.m_seta:
            return z3.If(z3.UGT(left, right), z3.BitVecVal(1, 32), z3.BitVecVal(0, 32))
        case ida_hexrays.m_setbE:
            return z3.If(z3.ULE(left, right), z3.BitVecVal(1, 32), z3.BitVecVal(0, 32))
        case ida_hexrays.m_setg:
            return z3.If(left > right, z3.BitVecVal(1, 32), z3.BitVecVal(0, 32))
        case ida_hexrays.m_setgE:
            return z3.If(left >= right, z3.BitVecVal(1, 32), z3.BitVecVal(0, 32))
        case ida_hexrays.m_setl:
            return z3.If(left < right, z3.BitVecVal(1, 32), z3.BitVecVal(0, 32))
        case ida_hexrays.m_setlE:
            return z3.If(left <= right, z3.BitVecVal(1, 32), z3.BitVecVal(0, 32))
        case ida_hexrays.m_setp:
            # 1) isolate the low byte
            lo_byte = typing.cast(z3.BitVecRef, z3.Extract(7, 0, left))
            # 2) XOR-reduce the eight single-bit slices to get 1 → odd, 0 → even
            bit0 = typing.cast(z3.BitVecRef, z3.Extract(0, 0, lo_byte))
            parity_bv = bit0  # 1-bit BitVec
            for i in range(1, 8):
                parity_bv = parity_bv ^ z3.Extract(i, i, lo_byte)
            # 3) PF is set (==1) when the parity is EVEN, i.e. parity_bv == 0
            pf_is_set = parity_bv == z3.BitVecVal(0, 1)  # Bool
            # 4) widen to 32-bit {1,0}
            return z3.If(pf_is_set, z3.BitVecVal(1, 32), z3.BitVecVal(0, 32))
        case ida_hexrays.m_sets:
            val = left  # BitVec(32)
            is_negative = val < z3.BitVecVal(
                0, 32
            )  # ordinary "<" is signed-less-than in Z3Py
            return z3.If(is_negative, z3.BitVecVal(1, 32), z3.BitVecVal(0, 32))
        case ida_hexrays.m_xdu | ida_hexrays.m_xds:
            # Extend or keep the same width; in our simplified model we just forward.
            return left
        case ida_hexrays.m_low:
            # Extract the lower half (dest_size) bits of the operand.
            dest_bits = (ast.dest_size or 4) * 8  # default 32-bit
            # Ensure we do not attempt to extract beyond the source width
            high_bit = min(dest_bits - 1, left.size() - 1)
            extracted = typing.cast(z3.BitVecRef, z3.Extract(high_bit, 0, left))
            # Zero-extend to 32-bit so subsequent operations (which assume 32-bit) do not
            # trigger sort-mismatch errors when combined with other 32-bit expressions.
            if extracted.size() < 32:
                extracted = typing.cast(
                    z3.BitVecRef, z3.ZeroExt(32 - extracted.size(), extracted)
                )
            return extracted
        case ida_hexrays.m_high:
            # Extract the upper half of the operand by shifting right by dest_bits
            dest_bits = (ast.dest_size or 4) * 8  # default 32-bit
            shifted = z3.LShR(left, dest_bits)
            high_bit = min(dest_bits - 1, shifted.size() - 1)
            extracted = typing.cast(z3.BitVecRef, z3.Extract(high_bit, 0, shifted))
            # Zero-extend to 32-bit for consistency with the rest of the engine.
            if extracted.size() < 32:
                extracted = typing.cast(
                    z3.BitVecRef, z3.ZeroExt(32 - extracted.size(), extracted)
                )
            return extracted
        case _:
            # Gracefully fail on unknown opcode; avoid type issues in logging
            op = getattr(ast, "opcode", None)
            op_str = opcode_to_string(int(op)) if isinstance(op, int) else str(op)
            raise D810Z3Exception(f"Z3 evaluation: Unknown opcode {op_str} for {ast}")


@requires_z3_installed
def mop_list_to_z3_expression_list(mop_list: list[ida_hexrays.mop_t]):
    if logger.debug_on:
        logger.debug(
            "mop_list_to_z3_expression_list: mop_list: %s",
            [format_mop_t(mop) for mop in mop_list],
        )
    ast_list = [mop_to_ast(mop) for mop in mop_list]
    ast_leaf_list = []
    for ast in ast_list:
        if ast is None:
            continue
        ast_leaf_list += ast.get_leaf_list()
    _ = create_z3_vars(ast_leaf_list)
    if logger.debug_on:
        logger.debug(
            "mop_list_to_z3_expression_list: ast_leaf_list: %s",
            ast_leaf_list,
        )
    return [ast_to_z3_expression(ast) for ast in ast_list]


# Module-level memoization for Z3 checks
_Z3_EQ_CACHE: Dict[Tuple[Tuple[int, int, int|str], Tuple[int, int, int|str]], bool] = {}


@requires_z3_installed
def z3_check_mop_equality(
    mop1: ida_hexrays.mop_t | None,
    mop2: ida_hexrays.mop_t | None,
    solver: z3.Solver | None = None,
) -> bool:
    if mop1 is None or mop2 is None:
        return False
    # TODO(w00tzenheimer): should we use this?
    # # Quick positives when both operands share type/size.
    # if mop1.t == mop2.t and mop1.size == mop2.size:
    #     if mop1.t == mop_n:
    #         return mop1.nnn.value == mop2.nnn.value
    #     if mop1.t == mop_r:
    #         return mop1.r == mop2.r
    #     if mop1.t == mop_S:
    #         # Direct comparison of stack var refs suffices.
    #         return mop1.s == mop2.s
    #     if mop1.t == mop_v:
    #         return mop1.g == mop2.g
    #     if mop1.t == mop_d:
    #         return mop1.dstr() == mop2.dstr()
    # If quick checks didn't decide, fall back to Z3 even when types differ.
    if logger.debug_on:
        logger.debug(
            "z3_check_mop_equality: mop1: %s, mop2: %s",
            format_mop_t(mop1),
            format_mop_t(mop2),
        )
        logger.debug(
            "z3_check_mop_equality:\n\tmop1.dstr(): %s\n\tmop2.dstr(): %s\n\thashes: %016X vs %016X",
            mop1.dstr(),
            mop2.dstr(),
            structural_mop_hash(mop1, 0),
            structural_mop_hash(mop2, 0),
        )
    # If pre-filters don't apply, fall back to Z3 with a memoized check keyed by
    # a cheap representation of the operands.
    try:
        k1 = (int(mop1.t), int(mop1.size), structural_mop_hash(mop1, 0))
        k2 = (int(mop2.t), int(mop2.size), structural_mop_hash(mop2, 0))
    except Exception:
        k1 = (int(mop1.t), int(mop1.size), mop1.dstr())
        k2 = (int(mop2.t), int(mop2.size), mop2.dstr())
    if k2 < k1:
        k1, k2 = k2, k1
    cache_key = (k1, k2)
    cached = _Z3_EQ_CACHE.get(cache_key)
    if cached is not None:
        return cached
    exprs = mop_list_to_z3_expression_list([mop1, mop2])
    if len(exprs) != 2:
        return False
    z3_mop1, z3_mop2 = exprs
    _solver = solver if solver is not None else get_solver()
    _solver.push()
    _solver.add(z3.Not(z3_mop1 == z3_mop2))
    is_equal = _solver.check() == z3.unsat
    _solver.pop()
    _Z3_EQ_CACHE[cache_key] = is_equal
    return is_equal


_Z3_NEQ_CACHE: Dict[Tuple[Tuple[int, int, int|str], Tuple[int, int, int|str]], bool] = {}


@requires_z3_installed
def z3_check_mop_inequality(
    mop1: ida_hexrays.mop_t | None,
    mop2: ida_hexrays.mop_t | None,
    solver: z3.Solver | None = None,
) -> bool:
    if mop1 is None or mop2 is None:
        return True
    # TODO(w00tzenheimer): should we use this?
    # if mop1.t == mop2.t and mop1.size == mop2.size:
    #     # Quick negatives when structure same.
    #     if mop1.t == mop_n:
    #         return mop1.nnn.value != mop2.nnn.value
    #     if mop1.t == mop_r:
    #         return mop1.r != mop2.r
    #     if mop1.t == mop_S:
    #         return mop1.s != mop2.s
    #     if mop1.t == mop_v:
    #         return mop1.g != mop2.g
    #     if mop1.t == mop_d:
    #         return mop1.dstr() != mop2.dstr()
    # Otherwise fall back to Z3 (also handles differing types).
    if logger.debug_on:
        logger.debug(
            "z3_check_mop_inequality: mop1: %s, mop2: %s",
            format_mop_t(mop1),
            format_mop_t(mop2),
        )
        logger.debug(
            "z3_check_mop_inequality:\n\tmop1.dstr(): %s\n\tmop2.dstr(): %s\n\thashes: %016X vs %016X",
            mop1.dstr(),
            mop2.dstr(),
            structural_mop_hash(mop1, 0),
            structural_mop_hash(mop2, 0),
        )
    # If pre-filters don't apply, fall back to Z3 with a memoized check keyed by
    # a cheap representation of the operands.
    try:
        k1 = (int(mop1.t), int(mop1.size), structural_mop_hash(mop1, 0))
        k2 = (int(mop2.t), int(mop2.size), structural_mop_hash(mop2, 0))
    except Exception:
        k1 = (int(mop1.t), int(mop1.size), mop1.dstr())
        k2 = (int(mop2.t), int(mop2.size), mop2.dstr())
    if k2 < k1:
        k1, k2 = k2, k1
    if k2 < k1:
        k1, k2 = k2, k1
    cache_key = (k1, k2)
    cached = _Z3_NEQ_CACHE.get(cache_key)
    if cached is not None:
        return cached
    exprs = mop_list_to_z3_expression_list([mop1, mop2])
    if len(exprs) != 2:
        return True
    z3_mop1, z3_mop2 = exprs
    _solver = solver if solver is not None else get_solver()
    _solver.push()
    _solver.add(z3_mop1 == z3_mop2)
    is_unequal = _solver.check() == z3.unsat
    _solver.pop()
    _Z3_NEQ_CACHE[cache_key] = is_unequal
    return is_unequal


@requires_z3_installed
def rename_leafs(leaf_list: list[AstLeaf]) -> list[str]:
    known_leaf_list = []
    for leaf in leaf_list:
        if leaf.is_constant() or leaf.mop is None:
            continue

        if leaf.mop.t == ida_hexrays.mop_z:
            continue

        leaf_index = get_mop_index(leaf.mop, known_leaf_list)
        if leaf_index == -1:
            known_leaf_list.append(leaf.mop)
            leaf_index = len(known_leaf_list) - 1
        leaf.z3_var_name = "x_{0}".format(leaf_index)

    return [
        "x_{0} = BitVec('x_{0}', {1})".format(i, 8 * leaf.size)
        for i, leaf in enumerate(known_leaf_list)
    ]


@requires_z3_installed
def log_z3_instructions(
    original_ins: ida_hexrays.minsn_t, new_ins: ida_hexrays.minsn_t
):
    orig_mba_tree = minsn_to_ast(original_ins)
    new_mba_tree = minsn_to_ast(new_ins)
    if orig_mba_tree is None or new_mba_tree is None:
        return None
    orig_leaf_list = orig_mba_tree.get_leaf_list()
    new_leaf_list = new_mba_tree.get_leaf_list()

    var_def_list = rename_leafs(orig_leaf_list + new_leaf_list)

    z3_file_logger.info(
        "print('Testing: {0} == {1}')".format(
            format_minsn_t(original_ins), format_minsn_t(new_ins)
        )
    )
    for var_def in var_def_list:
        z3_file_logger.info("{0}".format(var_def))

    removed_xdu = "{0}".format(orig_mba_tree).replace("xdu", "")
    z3_file_logger.info("original_expr = {0}".format(removed_xdu))
    removed_xdu = "{0}".format(new_mba_tree).replace("xdu", "")
    z3_file_logger.info("new_expr = {0}".format(removed_xdu))
    z3_file_logger.info("prove(original_expr == new_expr)\n")


@requires_z3_installed
def z3_prove_equivalence(
    pattern_ast: AstNode | AstLeaf,
    replacement_ast: AstNode | AstLeaf,
    z3_vars: dict[str, typing.Any] | None = None,
    constraints: list[typing.Any] | None = None,
    bit_width: int = 32,
) -> tuple[bool, dict[str, int] | None]:
    """Prove that two AST patterns are semantically equivalent using Z3.

    This function creates Z3 symbolic variables for each unique variable in the
    patterns, converts both patterns to Z3 expressions, and attempts to prove
    that they are equivalent for all possible variable values (subject to any
    provided constraints).

    Args:
        pattern_ast: The first AST pattern (typically the pattern to match).
        replacement_ast: The second AST pattern (typically the replacement).
        z3_vars: Optional pre-created Z3 variables mapping names to Z3 BitVec objects.
                 If None, variables will be created automatically.
        constraints: Optional list of Z3 constraint expressions that must hold for
                     the equivalence to be valid. For example, [c2 == ~c1] to indicate
                     that constant c2 must be the bitwise NOT of constant c1.
        bit_width: The bit width for symbolic variables (default 32).

    Returns:
        A tuple of (is_equivalent, counterexample):
        - is_equivalent: True if the patterns are proven equivalent, False otherwise.
        - counterexample: If not equivalent, a dict mapping variable names to values
                         that demonstrate the difference. None if equivalent.

    Example:
        >>> from d810.expr.ast import AstNode, AstLeaf
        >>> from ida_hexrays import m_add, m_sub, m_xor, m_or, m_and
        >>> # Pattern: (x | y) - (x & y)
        >>> pattern = AstNode(m_sub,
        ...     AstNode(m_or, AstLeaf("x"), AstLeaf("y")),
        ...     AstNode(m_and, AstLeaf("x"), AstLeaf("y")))
        >>> # Replacement: x ^ y
        >>> replacement = AstNode(m_xor, AstLeaf("x"), AstLeaf("y"))
        >>> is_equiv, counter = z3_prove_equivalence(pattern, replacement)
        >>> assert is_equiv  # These are mathematically equivalent
    """
    # Get all leaf nodes from both patterns to find variables
    pattern_leaves = pattern_ast.get_leaf_list()
    replacement_leaves = replacement_ast.get_leaf_list()
    all_leaves = pattern_leaves + replacement_leaves

    # If z3_vars not provided, create them
    if z3_vars is None:
        # Extract unique variable names (excluding constants)
        var_names = set()
        for leaf in all_leaves:
            if not leaf.is_constant() and hasattr(leaf, 'name'):
                var_names.add(leaf.name)

        # Create Z3 BitVec for each variable
        z3_vars = {name: z3.BitVec(name, bit_width) for name in sorted(var_names)}

        # Map the z3_vars to the leaves for conversion
        for leaf in all_leaves:
            if not leaf.is_constant() and hasattr(leaf, 'name') and leaf.name in z3_vars:
                leaf.z3_var = z3_vars[leaf.name]
                leaf.z3_var_name = leaf.name
    else:
        # Use provided z3_vars (includes both variables and pattern-matching constants)
        for leaf in all_leaves:
            if not hasattr(leaf, 'name'):
                continue

            # Assign z3_var to regular variables
            if not leaf.is_constant() and leaf.name in z3_vars:
                leaf.z3_var = z3_vars[leaf.name]
                leaf.z3_var_name = leaf.name
            # Also assign z3_var to pattern-matching constants (symbolic constants)
            elif leaf.is_constant() and leaf.name in z3_vars:
                # Pattern-matching constant like Const("c_1") - treat as symbolic
                if hasattr(leaf, 'expected_value') and leaf.expected_value is None:
                    leaf.z3_var = z3_vars[leaf.name]
                    leaf.z3_var_name = leaf.name

    # Convert both AST patterns to Z3 expressions
    try:
        pattern_z3 = ast_to_z3_expression(pattern_ast)
        replacement_z3 = ast_to_z3_expression(replacement_ast)
    except Exception as e:
        logger.error(
            "Failed to convert AST to Z3 expression: %s",
            e,
            exc_info=True,
        )
        return False, None

    # Create a solver and add constraints if any
    solver = z3.Solver()
    if constraints:
        for constraint in constraints:
            solver.add(constraint)

    # To prove equivalence, we check if NOT(pattern == replacement) is unsatisfiable
    # If it's unsatisfiable, then pattern == replacement for all valid inputs
    solver.add(z3.Not(pattern_z3 == replacement_z3))

    result = solver.check()

    if result == z3.unsat:
        # Patterns are equivalent
        return True, None
    elif result == z3.sat:
        # Patterns are NOT equivalent, get counterexample
        model = solver.model()
        counterexample = {}
        for var_name, var in z3_vars.items():
            if model[var] is not None:
                counterexample[var_name] = model[var].as_long()
        return False, counterexample
    else:
        # Unknown result (timeout, etc.)
        logger.warning("Z3 returned unknown result for equivalence check")
        return False, None
