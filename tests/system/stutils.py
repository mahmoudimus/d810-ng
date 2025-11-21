import contextlib
import logging
import os
import time
from typing import Optional

import idaapi
import idc

from d810.manager import D810State

logger = logging.getLogger(__name__)
from d810.optimizers.instrumentation import (
    DeobfuscationContext,
    get_current_deobfuscation_context,
    set_current_deobfuscation_context,
)


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
def d810_state(*, all_rules=False):
    """Context manager for D810 state with instrumentation support.

    This provides access to D810's deobfuscation engine and creates
    a DeobfuscationContext to track all optimization activity.

    Args:
        all_rules: If True, load ALL available rules (ignoring project config).
                   This is useful for testing refactored rules that aren't yet
                   in project configurations. Default: False (use project config).

    Usage:
        # Normal usage (project config filtering):
        with d810_state() as state:
            state.stop_d810()
            # ... decompile without d810 ...

            state.start_d810()
            # ... decompile with d810 ...

        # Testing with all rules (no filtering):
        with d810_state(all_rules=True) as state:
            # All registered rules will be active, including refactored ones
            state.start_d810()
            # ...

            # Access instrumentation
            ctx = get_current_deobfuscation_context()
            assert ctx.rule_fired("Xor_HackersDelight1")  # Refactored rule!
    """
    state = D810State()  # singleton
    if not (was_loaded := state.is_loaded()):
        t_load_start = time.perf_counter()
        state.load(gui=False)
        t_load = time.perf_counter() - t_load_start
        print(f"  ⏱ D810State.load() took {t_load:.2f}s")

    # Override rule selection for testing
    if all_rules:
        # Bypass project config filtering - use ALL registered rules
        # This allows testing of refactored rules that aren't in configs yet
        state.current_ins_rules = state.known_ins_rules
        state.current_blk_rules = state.known_blk_rules
        logger.debug(f"all_rules=True: Loaded {len(state.current_ins_rules)} instruction rules (bypassing project config)")

    if not (was_started := state.manager.started):
        t_start = time.perf_counter()
        state.start_d810()
        t_start_elapsed = time.perf_counter() - t_start
        print(f"  ⏱ D810State.start_d810() took {t_start_elapsed:.2f}s")

    # Create a new deobfuscation context for this session
    ctx = DeobfuscationContext()
    set_current_deobfuscation_context(ctx)

    # Hook the context into the manager for instrumentation
    # The manager will populate it during optimization
    state.manager._deobfuscation_context = ctx

    try:
        yield state
    finally:
        if not was_started:
            state.stop_d810()
        if not was_loaded:
            state.unload(gui=False)

        # Context remains accessible after the block for assertions
        # It will be reset on next d810_state() call
