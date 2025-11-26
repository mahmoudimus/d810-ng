#!/usr/bin/env python3
"""Fix remaining unqualified ida_hexrays symbols in partially converted files.

This script prefixes unqualified ida_hexrays symbols with 'ida_hexrays.'
even in files that already have 'import ida_hexrays'.
"""

import re
import sys
from pathlib import Path

# Symbols exported by ida_hexrays that need to be prefixed
IDA_HEXRAYS_SYMBOLS = [
    # Types/Classes
    "mba_t", "mbl_array_t", "mblock_t", "minsn_t", "mop_t", "mlist_t",
    "optinsn_t", "optblock_t", "minsn_visitor_t", "mop_visitor_t",
    "Hexrays_Hooks", "cfunc_t", "cinsn_t", "cexpr_t", "citem_t",
    "vd_printer_t", "qstring", "carglist_t", "carg_t", "lvars_t", "lvar_t",
    "mcallinfo_t", "mcallarg_t", "mba_ranges_t", "bitset_t", "vivl_t",
    "vdloc_t", "scif_t", "fnumber_t", "hexwarns_t", "minsn_access_t",
    "chain_t", "block_chains_t", "graph_chains_t",

    # mop types
    "mop_z", "mop_r", "mop_n", "mop_str", "mop_d", "mop_S", "mop_v",
    "mop_b", "mop_f", "mop_l", "mop_a", "mop_h", "mop_c", "mop_fn",
    "mop_p", "mop_sc",

    # Maturity levels
    "MMAT_ZERO", "MMAT_GENERATED", "MMAT_PREOPTIMIZED", "MMAT_LOCOPT",
    "MMAT_CALLS", "MMAT_GLBOPT1", "MMAT_GLBOPT2", "MMAT_GLBOPT3",
    "MMAT_LVARS",

    # Block types
    "BLT_NONE", "BLT_STOP", "BLT_0WAY", "BLT_1WAY", "BLT_2WAY", "BLT_NWAY", "BLT_XTRN",

    # Block flags
    "MBL_PRIV", "MBL_NONFAKE", "MBL_DEAD", "MBL_NORET", "MBL_FAKE", "MBL_GOTO",
    "MBL_TCAL", "MBL_PUSH", "MBL_DMT64", "MBL_COMB", "MBL_PROP", "MBL_CALL",
    "MBL_BACKPROP", "MBL_VALRANGES",

    # Opcodes (m_*)
    "m_nop", "m_stx", "m_ldx", "m_ldc", "m_mov", "m_neg", "m_lnot", "m_bnot",
    "m_xds", "m_xdu", "m_low", "m_high", "m_add", "m_sub", "m_mul", "m_udiv",
    "m_sdiv", "m_umod", "m_smod", "m_or", "m_and", "m_xor", "m_shl", "m_shr",
    "m_sar", "m_cfadd", "m_ofadd", "m_cfshl", "m_cfshr", "m_sets", "m_seto",
    "m_setp", "m_setnz", "m_setz", "m_setae", "m_setb", "m_seta", "m_setbe",
    "m_setg", "m_setge", "m_setl", "m_setle", "m_jcnd", "m_jnz", "m_jz",
    "m_jae", "m_jb", "m_ja", "m_jbe", "m_jg", "m_jge", "m_jl", "m_jle",
    "m_jtbl", "m_ijmp", "m_goto", "m_call", "m_ret", "m_push", "m_pop",
    "m_und", "m_ext", "m_f2i", "m_f2u", "m_i2f", "m_u2f", "m_f2f", "m_fneg",
    "m_fadd", "m_fsub", "m_fmul", "m_fdiv",

    # Access flags
    "MUST_ACCESS", "MAY_ACCESS", "FULL_XDSU",

    # Functions
    "is_mcode_jcond", "is_mcode_set", "is_mcode_j1", "is_mcode_xdsu",
    "is_mcode_call", "is_mcode_fpu", "is_mcode_commutative",
    "get_mreg_name", "get_dtype_name", "get_mopt_name", "get_mcode_name",
    "init_hexrays_plugin", "term_hexrays_plugin", "open_pseudocode",
    "decompile", "decompile_func", "gen_microcode",
    "hexrays_failure_t", "vd_failure_t", "merror_t",
]


def fix_symbols(filepath: Path) -> bool:
    """Fix remaining unqualified ida_hexrays symbols in a file."""
    content = filepath.read_text()
    original = content

    # Only process files that have 'import ida_hexrays'
    if "import ida_hexrays" not in content:
        print(f"  Skipping {filepath.name} - no ida_hexrays import")
        return False

    # Build regex pattern for symbols
    for symbol in IDA_HEXRAYS_SYMBOLS:
        # Pattern to match symbol not already prefixed with ida_hexrays.
        # Use negative lookbehind for 'ida_hexrays.' and word boundaries
        pattern = rf'(?<!ida_hexrays\.)(?<![a-zA-Z_]){re.escape(symbol)}(?![a-zA-Z0-9_])'
        replacement = f'ida_hexrays.{symbol}'
        content = re.sub(pattern, replacement, content)

    if content != original:
        filepath.write_text(content)
        print(f"  Fixed {filepath.name}")
        return True
    else:
        print(f"  No changes needed for {filepath.name}")
        return False


def main():
    if len(sys.argv) < 2:
        print("Usage: python fix_remaining_symbols.py <file_or_directory>")
        sys.exit(1)

    target = Path(sys.argv[1])

    if target.is_file():
        fix_symbols(target)
    elif target.is_dir():
        for pyfile in target.rglob("*.py"):
            fix_symbols(pyfile)
    else:
        print(f"Error: {target} not found")
        sys.exit(1)


if __name__ == "__main__":
    main()
