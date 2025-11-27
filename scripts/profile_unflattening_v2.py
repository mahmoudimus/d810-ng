#!/usr/bin/env python3
"""Compare FixPredecessorOfConditionalJumpBlock V1 vs V2 performance.

Usage:
    PYTHONPATH=src python scripts/profile_unflattening_v2.py
"""

import time
import sys
from pathlib import Path

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


def generate_microcode(func_ea: int):
    """Generate microcode at MMAT_CALLS."""
    import ida_hexrays
    import idaapi

    func = idaapi.get_func(func_ea)
    if func is None:
        raise ValueError(f"No function at 0x{func_ea:x}")

    mbr = idaapi.mba_ranges_t()
    mbr.ranges.push_back(idaapi.range_t(func.start_ea, func.end_ea))
    hf = idaapi.hexrays_failure_t()

    mba = idaapi.gen_microcode(
        mbr, hf, None, idaapi.DECOMP_NO_WAIT, ida_hexrays.MMAT_CALLS
    )

    if mba is None:
        raise ValueError(f"Failed to generate microcode: {hf.desc()}")

    return mba


def run_rule_v1(mba, max_passes: int = 10):
    """Run original V1 rule."""
    import ida_hexrays
    from d810.optimizers.microcode.flow.flattening.fix_pred_cond_jump_block import (
        FixPredecessorOfConditionalJumpBlock,
    )
    from d810.hexrays.tracker import MopTracker

    rule = FixPredecessorOfConditionalJumpBlock()
    rule.maturities = [ida_hexrays.MMAT_CALLS]
    rule.cur_maturity = ida_hexrays.MMAT_CALLS
    rule.cur_maturity_pass = 0
    rule.dump_intermediate_microcode = False

    total_changes = 0
    pass_num = 0

    while pass_num < max_passes:
        pass_changes = 0
        MopTracker.reset()

        for i in range(mba.qty):
            blk = mba.get_mblock(i)
            if blk is None:
                continue
            changes = rule.optimize(blk)
            pass_changes += changes

        total_changes += pass_changes
        if pass_changes == 0:
            break
        pass_num += 1

    return total_changes, pass_num + 1


def run_rule_v2(mba, max_passes: int = 10):
    """Run optimized V2 rule."""
    import ida_hexrays
    from d810.optimizers.microcode.flow.flattening.fix_pred_cond_jump_block_v2 import (
        FixPredecessorOfConditionalJumpBlockV2,
        clear_cache,
        get_cache_stats,
    )
    from d810.hexrays.tracker import MopTracker

    clear_cache()  # Start fresh

    rule = FixPredecessorOfConditionalJumpBlockV2()
    rule.maturities = [ida_hexrays.MMAT_CALLS]
    rule.cur_maturity = ida_hexrays.MMAT_CALLS
    rule.cur_maturity_pass = 0
    rule.dump_intermediate_microcode = False

    total_changes = 0
    pass_num = 0

    while pass_num < max_passes:
        pass_changes = 0
        MopTracker.reset()

        for i in range(mba.qty):
            blk = mba.get_mblock(i)
            if blk is None:
                continue
            changes = rule.optimize(blk)
            pass_changes += changes

        total_changes += pass_changes
        if pass_changes == 0:
            break
        pass_num += 1

    cache_stats = get_cache_stats()
    return total_changes, pass_num + 1, cache_stats


def main():
    print("=" * 80)
    print("COMPARING V1 vs V2 FixPredecessorOfConditionalJumpBlock")
    print("=" * 80)

    func_ea = setup_ida()
    print(f"Target function: 0x{func_ea:x} (_hodur_func)")

    # Run V1
    print("\n" + "-" * 40)
    print("Running V1 (original)...")
    print("-" * 40)

    mba = generate_microcode(func_ea)
    print(f"Generated microcode: {mba.qty} blocks")

    start = time.perf_counter()
    v1_changes, v1_passes = run_rule_v1(mba, max_passes=5)
    v1_time = time.perf_counter() - start

    print(f"V1: {v1_changes} changes in {v1_passes} passes, {v1_time:.3f}s")

    # Run V2
    print("\n" + "-" * 40)
    print("Running V2 (optimized)...")
    print("-" * 40)

    mba = generate_microcode(func_ea)  # Fresh microcode
    print(f"Generated microcode: {mba.qty} blocks")

    start = time.perf_counter()
    v2_changes, v2_passes, cache_stats = run_rule_v2(mba, max_passes=5)
    v2_time = time.perf_counter() - start

    print(f"V2: {v2_changes} changes in {v2_passes} passes, {v2_time:.3f}s")
    print(f"Cache stats: {cache_stats}")

    # Summary
    print("\n" + "=" * 80)
    print("SUMMARY")
    print("=" * 80)
    print(f"V1: {v1_time:.3f}s ({v1_changes} changes, {v1_passes} passes)")
    print(f"V2: {v2_time:.3f}s ({v2_changes} changes, {v2_passes} passes)")

    if v2_time > 0:
        speedup = v1_time / v2_time
        print(f"\nSpeedup: {speedup:.2f}x")
    else:
        print("\nV2 too fast to measure!")

    if v1_changes != v2_changes:
        print(f"\n⚠️  WARNING: Different number of changes! V1={v1_changes}, V2={v2_changes}")
    else:
        print(f"\n✅ Both versions made the same number of changes ({v1_changes})")


if __name__ == "__main__":
    main()
