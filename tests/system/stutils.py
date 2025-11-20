import contextlib
import os

import idaapi
import idc

from d810.manager import D810State


def configure_hexrays_for_consistent_output():
    """Configure Hex-Rays decompiler settings for consistent test output.

    Sets comprehensive configuration to ensure decompiled pseudocode is consistent
    across different IDA Pro versions and environments.
    """
    # Formatting and display settings
    idaapi.change_hexrays_config("RIGHT_MARGIN = 100")  # Start wrapping near 100 columns
    idaapi.change_hexrays_config("PSEUDOCODE_SYNCED = YES")  # Sync with disassembly
    idaapi.change_hexrays_config("PSEUDOCODE_DOCKPOS = DP_RIGHT")  # Dock at right margin
    idaapi.change_hexrays_config("GENERATE_EMPTY_LINES = YES")  # Add empty lines between blocks
    idaapi.change_hexrays_config("BLOCK_INDENT = 4")  # Indent blocks with 4 spaces

    # Function size and complexity limits
    idaapi.change_hexrays_config("MAX_FUNCSIZE = 2048")  # Max function size
    idaapi.change_hexrays_config("MAX_NCOMMAS = 1")  # Max commas in expressions

    # Variable and label display
    idaapi.change_hexrays_config("COLLAPSE_LVARS = YES")  # Collapse local variables
    idaapi.change_hexrays_config("GENERATE_EA_LABELS = YES")  # Generate EA labels
    idaapi.change_hexrays_config("AUTO_UNHIDE = YES")  # Auto-unhide code

    # Number display format - CRITICAL for consistent test output
    idaapi.change_hexrays_config("DEFAULT_RADIX = 16")  # Hexadecimal for all constants
    # Note: DEFAULT_RADIX values:
    #   0 = decimal for signed, hex for unsigned (variable)
    #   10 = decimal for all
    #   16 = hexadecimal for all (most consistent for tests)


def pseudocode_to_string(pseudo_code: idaapi.strvec_t) -> str:
    """Convert IDA pseudocode to a plain string without formatting tags.

    Args:
        pseudo_code: IDA pseudocode strvec_t object

    Returns:
        Plain text representation of the pseudocode
    """
    converted_obj: list[str] = [
        idaapi.tag_remove(line_obj.line) for line_obj in pseudo_code
    ]

    return os.linesep.join(converted_obj)


def setup_libobfuscated_function_names():
    """
    Set up function names for libobfuscated.dll based on the IDA Pro function table.
    This is needed because the DLL doesn't export function names, so we need to
    manually assign them in IDA's database.
    """
    # Function addresses from IDA Pro function table for libofuscated.dll
    # Format: name -> address
    function_map = {
        "constant_folding_test1": 0x180001000,
        "constant_folding_test2": 0x1800015C0,
        "outlined_helper_1": 0x1800016A0,
        "outlined_helper_2": 0x1800016D0,
        "AntiDebug_ExceptionFilter": 0x180001710,
        "test_chained_add": 0x180006630,
        "test_cst_simplification": 0x180006680,
        "test_opaque_predicate": 0x180006780,
        "test_xor": 0x180006920,
        "test_mba_guessing": 0x1800069A0,
        "test_function_ollvm_fla_bcf_sub": 0x180006B40,
        "tigress_minmaxarray": 0x180009490,
        "unwrap_loops": 0x180009730,
        "unwrap_loops_2": 0x1800097E0,
        "unwrap_loops_3": 0x1800098C0,
        "while_switch_flattened": 0x1800099F0,
        "NtCurrentTeb": 0x180009B30,
    }

    for name, addr in function_map.items():
        # Set the function name at the given address
        idc.set_name(addr, name, idc.SN_NOWARN | idc.SN_NOCHECK)
        # Make sure it's recognized as a function
        if not idc.get_func_attr(addr, idc.FUNCATTR_START):
            idc.create_insn(addr)
            idaapi.add_func(addr)


@contextlib.contextmanager
def d810_state():
    state = D810State()  # singleton
    if not (was_loaded := state.is_loaded()):
        state.load(gui=False)
    if not (was_started := state.manager.started):
        state.start_d810()
    yield state
    if not was_started:
        state.stop_d810()
    if not was_loaded:
        state.unload(gui=False)
