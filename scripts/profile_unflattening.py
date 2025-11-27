#!/usr/bin/env python3
"""Profile FixPredecessorOfConditionalJumpBlock on hodur_func.

This script profiles the unflattening rule to identify performance bottlenecks.

Usage:
    PYTHONPATH=src python scripts/profile_unflattening.py

Outputs:
    - pyinstrument HTML report: /tmp/hodur_profile.html
    - cProfile stats: /tmp/hodur_cprofile.prof
    - Top 50 functions by cumulative time
"""

import cProfile
import pstats
import io
import sys
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent / "src"))


def setup_ida():
    """Initialize IDA and open the test binary."""
    import idapro

    binary_path = Path(__file__).parent.parent / "samples" / "bins" / "libobfuscated.dylib"
    print(f"Opening {binary_path}...")
    idapro.open_database(str(binary_path), run_auto_analysis=True)

    import idaapi
    if not idaapi.init_hexrays_plugin():
        raise RuntimeError("Hex-Rays decompiler not available")

    return 0x5680  # _hodur_func address


def run_unflattening(func_ea: int, max_passes: int = 10):
    """Run FixPredecessorOfConditionalJumpBlock on the function."""
    import ida_hexrays
    import idaapi

    from d810.optimizers.microcode.flow.flattening.fix_pred_cond_jump_block import (
        FixPredecessorOfConditionalJumpBlock,
    )
    from d810.hexrays.tracker import MopTracker

    # Get the microcode
    func = idaapi.get_func(func_ea)
    if func is None:
        raise ValueError(f"No function at 0x{func_ea:x}")

    # Generate microcode at MMAT_CALLS (where unflattening typically runs)
    mbr = idaapi.mba_ranges_t()
    mbr.ranges.push_back(idaapi.range_t(func.start_ea, func.end_ea))
    hf = idaapi.hexrays_failure_t()

    mba = idaapi.gen_microcode(
        mbr, hf, None, idaapi.DECOMP_NO_WAIT, ida_hexrays.MMAT_CALLS
    )

    if mba is None:
        raise ValueError(f"Failed to generate microcode: {hf.desc()}")

    print(f"Generated microcode: {mba.qty} blocks at maturity {mba.maturity}")

    # Create and configure the rule
    rule = FixPredecessorOfConditionalJumpBlock()
    rule.maturities = [ida_hexrays.MMAT_CALLS]
    rule.cur_maturity = ida_hexrays.MMAT_CALLS
    rule.cur_maturity_pass = 0
    rule.dump_intermediate_microcode = False

    # Run the rule on each block
    total_changes = 0
    pass_num = 0

    while pass_num < max_passes:
        pass_changes = 0
        MopTracker.reset()  # Reset path counter

        for i in range(mba.qty):
            blk = mba.get_mblock(i)
            if blk is None:
                continue

            changes = rule.optimize(blk)
            pass_changes += changes

        print(f"Pass {pass_num}: {pass_changes} changes")
        total_changes += pass_changes

        if pass_changes == 0:
            break

        pass_num += 1

    print(f"Total changes: {total_changes} in {pass_num + 1} passes")
    return total_changes


def profile_with_pyinstrument(func_ea: int):
    """Profile using pyinstrument for a flame graph view."""
    try:
        from pyinstrument import Profiler
    except ImportError:
        print("pyinstrument not installed, skipping")
        return

    profiler = Profiler()
    profiler.start()

    try:
        run_unflattening(func_ea, max_passes=3)
    finally:
        profiler.stop()

    # Save HTML report
    html_path = "/tmp/hodur_profile.html"
    with open(html_path, "w") as f:
        f.write(profiler.output_html())
    print(f"\nPyinstrument HTML report: {html_path}")

    # Print text summary
    print("\n" + "=" * 80)
    print("PYINSTRUMENT SUMMARY")
    print("=" * 80)
    print(profiler.output_text(unicode=True, color=False))


def profile_with_cprofile(func_ea: int):
    """Profile using cProfile for detailed stats."""
    profiler = cProfile.Profile()
    profiler.enable()

    try:
        run_unflattening(func_ea, max_passes=3)
    finally:
        profiler.disable()

    # Save binary stats
    prof_path = "/tmp/hodur_cprofile.prof"
    profiler.dump_stats(prof_path)
    print(f"\ncProfile stats saved to: {prof_path}")
    print("View with: python -m pstats /tmp/hodur_cprofile.prof")
    print("Or: snakeviz /tmp/hodur_cprofile.prof")

    # Print top functions by cumulative time
    print("\n" + "=" * 80)
    print("TOP 50 FUNCTIONS BY CUMULATIVE TIME")
    print("=" * 80)

    stream = io.StringIO()
    stats = pstats.Stats(profiler, stream=stream)
    stats.sort_stats("cumulative")
    stats.print_stats(50)
    print(stream.getvalue())

    # Print top functions by total time (time spent in function itself)
    print("\n" + "=" * 80)
    print("TOP 50 FUNCTIONS BY TOTAL TIME (in function itself)")
    print("=" * 80)

    stream = io.StringIO()
    stats = pstats.Stats(profiler, stream=stream)
    stats.sort_stats("tottime")
    stats.print_stats(50)
    print(stream.getvalue())

    # Print callers of key functions
    print("\n" + "=" * 80)
    print("WHO CALLS get_mop_index?")
    print("=" * 80)
    stream = io.StringIO()
    stats = pstats.Stats(profiler, stream=stream)
    stats.print_callers("get_mop_index")
    print(stream.getvalue())

    print("\n" + "=" * 80)
    print("WHO CALLS equal_mops_ignore_size?")
    print("=" * 80)
    stream = io.StringIO()
    stats = pstats.Stats(profiler, stream=stream)
    stats.print_callers("equal_mops_ignore_size")
    print(stream.getvalue())

    print("\n" + "=" * 80)
    print("WHO CALLS search_backward?")
    print("=" * 80)
    stream = io.StringIO()
    stats = pstats.Stats(profiler, stream=stream)
    stats.print_callers("search_backward")
    print(stream.getvalue())


def main():
    print("=" * 80)
    print("PROFILING FixPredecessorOfConditionalJumpBlock on _hodur_func")
    print("=" * 80)

    func_ea = setup_ida()
    print(f"Target function: 0x{func_ea:x}")

    # Run with pyinstrument first (gives nice visual output)
    print("\n" + "=" * 80)
    print("PROFILING WITH PYINSTRUMENT")
    print("=" * 80)
    profile_with_pyinstrument(func_ea)

    # Run with cProfile for detailed stats
    print("\n" + "=" * 80)
    print("PROFILING WITH CPROFILE")
    print("=" * 80)
    profile_with_cprofile(func_ea)


if __name__ == "__main__":
    main()
