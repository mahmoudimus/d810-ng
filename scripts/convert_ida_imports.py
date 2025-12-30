#!/usr/bin/env python3
"""Convert 'from ida_hexrays import *' to qualified 'import ida_hexrays' imports.

Uses libcst for safe AST-based transformation that preserves formatting.
"""

import sys
from pathlib import Path

import libcst as cst


# Symbols exported by ida_hexrays that need to be prefixed
IDA_HEXRAYS_SYMBOLS = {
    # Types/Classes
    "mba_t", "mbl_array_t", "mblock_t", "minsn_t", "mop_t", "mlist_t",
    "optinsn_t", "optblock_t", "minsn_visitor_t", "mop_visitor_t",
    "Hexrays_Hooks", "cfunc_t", "cinsn_t", "cexpr_t", "citem_t",
    "vd_printer_t", "qstring", "carglist_t", "carg_t", "lvars_t", "lvar_t",
    "mcallinfo_t", "mcallarg_t", "mba_ranges_t", "bitset_t", "vivl_t",
    "vdloc_t", "scif_t", "fnumber_t", "hexwarns_t", "minsn_access_t",
    "chain_t", "block_chains_t", "graph_chains_t", "control_graph_t",

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
}


class IdaHexraysTransformer(cst.CSTTransformer):
    """Transform unqualified ida_hexrays symbols to qualified form."""

    def __init__(self):
        super().__init__()
        self.modified = False

    def leave_ImportFrom(
        self, original_node: cst.ImportFrom, updated_node: cst.ImportFrom
    ) -> cst.CSTNode:
        """Replace 'from ida_hexrays import *' with 'import ida_hexrays'."""
        if (
            isinstance(updated_node.module, cst.Name)
            and updated_node.module.value == "ida_hexrays"
            and isinstance(updated_node.names, cst.ImportStar)
        ):
            self.modified = True
            # Return just the Import statement, preserving leading lines
            return cst.Import(
                names=[cst.ImportAlias(name=cst.Name("ida_hexrays"))]
            )
        return updated_node

    def leave_Name(
        self, original_node: cst.Name, updated_node: cst.Name
    ) -> cst.BaseExpression:
        """Replace unqualified ida_hexrays symbols with qualified form."""
        if updated_node.value in IDA_HEXRAYS_SYMBOLS:
            self.modified = True
            return cst.Attribute(
                value=cst.Name("ida_hexrays"),
                attr=cst.Name(updated_node.value),
            )
        return updated_node

    def leave_Attribute(
        self, original_node: cst.Attribute, updated_node: cst.Attribute
    ) -> cst.BaseExpression:
        """Don't double-qualify already qualified symbols."""
        # If the value is ida_hexrays and attr was transformed, undo transformation
        if isinstance(updated_node.value, cst.Name) and updated_node.value.value == "ida_hexrays":
            # Check if attr is an Attribute (would mean double qualification)
            if isinstance(updated_node.attr, cst.Attribute):
                # ida_hexrays.(ida_hexrays.X) -> ida_hexrays.X
                return cst.Attribute(
                    value=cst.Name("ida_hexrays"),
                    attr=updated_node.attr.attr,
                )
        return updated_node


def convert_file(filepath: Path) -> bool:
    """Convert a single file using libcst."""
    try:
        content = filepath.read_text()

        # Quick check - skip if no ida_hexrays reference at all
        if "ida_hexrays" not in content and not any(
            sym in content for sym in ["mblock_t", "minsn_t", "mop_t", "m_add", "m_sub"]
        ):
            return False

        tree = cst.parse_module(content)
        transformer = IdaHexraysTransformer()
        new_tree = tree.visit(transformer)

        if transformer.modified:
            filepath.write_text(new_tree.code)
            print(f"  Converted {filepath.name}")
            return True
        else:
            print(f"  No changes needed for {filepath.name}")
            return False

    except cst.ParserSyntaxError as e:
        print(f"  Syntax error in {filepath.name}: {e}")
        return False
    except Exception as e:
        print(f"  Error processing {filepath.name}: {e}")
        import traceback
        traceback.print_exc()
        return False


def main():
    if len(sys.argv) < 2:
        print("Usage: python convert_ida_imports.py <file_or_directory>")
        sys.exit(1)

    target = Path(sys.argv[1])

    if target.is_file():
        convert_file(target)
    elif target.is_dir():
        for pyfile in sorted(target.rglob("*.py")):
            convert_file(pyfile)
    else:
        print(f"Error: {target} not found")
        sys.exit(1)


if __name__ == "__main__":
    main()
