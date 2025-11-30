"""Minimal reproducible test to debug why VerifiableRule subclasses don't fire.

This test creates a simple scenario to trace exactly where the rule matching fails.
"""
import idapro
import sys
import logging

# Set up detailed logging
logging.basicConfig(
    level=logging.DEBUG,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)

sys.path.insert(0, '/home/user/d810-ng/src')

# Import d810 components
from d810.optimizers.rules import VerifiableRule
from d810.optimizers.microcode.instructions.handler import InstructionOptimizationRule
from d810.optimizers.microcode.instructions.pattern_matching.handler import PatternMatchingRule
import idaapi
from ida_hexrays import *

print("=" * 80)
print("STEP 1: Check VerifiableRule inheritance")
print("=" * 80)
print(f"VerifiableRule.__bases__: {VerifiableRule.__bases__}")
print(f"VerifiableRule.__mro__: {[c.__name__ for c in VerifiableRule.__mro__]}")
print(f"Is VerifiableRule a subclass of PatternMatchingRule? {issubclass(VerifiableRule, PatternMatchingRule)}")

print("\n" + "=" * 80)
print("STEP 2: Check registered rules")
print("=" * 80)
all_rules = InstructionOptimizationRule.all()
print(f"Total rules in registry: {len(all_rules)}")

verifiable_rules = [r for r in all_rules if isinstance(r, type) and issubclass(r, VerifiableRule)]
print(f"VerifiableRule subclasses: {len(verifiable_rules)}")

xor_hd3_rules = [r for r in verifiable_rules if r.__name__ == 'Xor_HackersDelightRule_3']
print(f"\nFound Xor_HackersDelightRule_3: {len(xor_hd3_rules)}")
if xor_hd3_rules:
    rule_cls = xor_hd3_rules[0]
    print(f"  Class: {rule_cls}")
    print(f"  Module: {rule_cls.__module__}")
    print(f"  Bases: {rule_cls.__bases__}")
    print(f"  Is PatternMatchingRule: {issubclass(rule_cls, PatternMatchingRule)}")

print("\n" + "=" * 80)
print("STEP 3: Check if rule has required methods")
print("=" * 80)
if xor_hd3_rules:
    rule_cls = xor_hd3_rules[0]
    methods = ['match', 'replace', 'check', 'get_pattern', 'get_replacement']
    for method_name in methods:
        has_method = hasattr(rule_cls, method_name)
        print(f"  {method_name}: {'✓' if has_method else '✗'}")
        if has_method:
            method = getattr(rule_cls, method_name)
            print(f"    {method}")

print("\n" + "=" * 80)
print("STEP 4: Try to instantiate the rule")
print("=" * 80)
if xor_hd3_rules:
    rule_cls = xor_hd3_rules[0]
    try:
        # Check if we can instantiate it
        import inspect
        sig = inspect.signature(rule_cls.__init__)
        print(f"  __init__ signature: {sig}")

        # Try to create instance
        rule_instance = rule_cls()
        print(f"  ✓ Successfully instantiated: {rule_instance}")
        print(f"  Rule name: {rule_instance.name}")

        # Check pattern and replacement
        if hasattr(rule_instance, 'PATTERN'):
            print(f"  PATTERN: {rule_instance.PATTERN}")
        if hasattr(rule_instance, 'REPLACEMENT'):
            print(f"  REPLACEMENT: {rule_instance.REPLACEMENT}")

    except Exception as e:
        print(f"  ✗ Failed to instantiate: {e}")
        import traceback
        traceback.print_exc()

print("\n" + "=" * 80)
print("STEP 5: Check PatternOptimizer usage")
print("=" * 80)
from d810.optimizers.microcode.instructions.pattern_matching.handler import PatternOptimizer

# Create a PatternOptimizer instance
try:
    import pathlib
    log_dir = pathlib.Path("/tmp/d810_debug")
    log_dir.mkdir(exist_ok=True)

    pattern_opt = PatternOptimizer(log_dir)
    print(f"  ✓ Created PatternOptimizer: {pattern_opt}")
    print(f"  Name: {pattern_opt.name}")

    # Check if it has rules
    print(f"  Rules in optimizer: {len(pattern_opt.rules)}")

    # Try to add our rule
    if xor_hd3_rules:
        rule_cls = xor_hd3_rules[0]
        try:
            rule_instance = rule_cls()
            success = pattern_opt.add_rule(rule_instance)
            print(f"  add_rule() returned: {success}")
            print(f"  Rules after add: {len(pattern_opt.rules)}")

            # Check if it's in the rules set
            if rule_instance in pattern_opt.rules:
                print(f"  ✓ Rule is in optimizer.rules")
            else:
                print(f"  ✗ Rule NOT in optimizer.rules")
                print(f"  Rules set: {pattern_opt.rules}")
        except Exception as e:
            print(f"  ✗ Failed to add rule: {e}")
            import traceback
            traceback.print_exc()

except Exception as e:
    print(f"  ✗ Failed to create PatternOptimizer: {e}")
    import traceback
    traceback.print_exc()

print("\n" + "=" * 80)
print("STEP 6: Check if rule can match a simple pattern")
print("=" * 80)

# Open the test binary
binary_path = "/home/user/d810-ng/samples/bins/libobfuscated.dll"
import tempfile
import shutil
temp_dir = tempfile.mkdtemp()
temp_binary = shutil.copy(binary_path, temp_dir)
print(f"Opening binary: {temp_binary}")

try:
    idaapi.open_database(temp_binary, idaapi.OOPENFLAG_NODELETEDB)
    print("  ✓ Database opened")

    # Find test_xor function
    func_ea = idaapi.get_name_ea(idaapi.BADADDR, "test_xor")
    print(f"  test_xor function at: {hex(func_ea)}")

    if func_ea != idaapi.BADADDR:
        # Get function microcode
        func = idaapi.get_func(func_ea)
        if func:
            print(f"  ✓ Found function: {func}")

            # Try to get hexrays output
            try:
                mbr = idaapi.mba_ranges_t()
                mbr.ranges.push_back(idaapi.range_t(func.start_ea, func.end_ea))
                hf = idaapi.hexrays_failure_t()
                mba = idaapi.gen_microcode(mbr, hf, None, idaapi.DECOMP_WARNINGS, idaapi.MMAT_GLBOPT1)

                if mba:
                    print(f"  ✓ Generated microcode: {mba}")
                    print(f"  Maturity: {mba.maturity}")
                    print(f"  Number of blocks: {mba.qty}")

                    # Look at instructions in first block
                    if mba.qty > 0:
                        blk = mba.get_mblock(0)
                        print(f"\n  Instructions in block 0:")
                        for i in range(min(blk.head.serial, 10)):
                            ins = blk.head
                            # Walk to instruction i
                            for _ in range(i):
                                if ins:
                                    ins = ins.next
                            if ins:
                                from d810.hexrays.hexrays_formatters import format_minsn_t
                                print(f"    {i}: {format_minsn_t(ins)}")

                                # Check if this matches our pattern: (x + y) - 2*(x & y)
                                if ins.opcode == m_sub:
                                    print(f"      Found SUB instruction!")
                                    print(f"      Left: {format_minsn_t(ins.l) if ins.l else 'None'}")
                                    print(f"      Right: {format_minsn_t(ins.r) if ins.r else 'None'}")

                                    # Try to match with our rule
                                    if xor_hd3_rules and pattern_opt.rules:
                                        rule_instance = list(pattern_opt.rules)[0]
                                        print(f"\n      Testing pattern match with {rule_instance.name}...")
                                        try:
                                            # Check if rule can match this instruction
                                            if hasattr(rule_instance, 'match'):
                                                match_result = rule_instance.match(ins)
                                                print(f"      match() returned: {match_result}")
                                            if hasattr(rule_instance, 'check'):
                                                check_result = rule_instance.check(ins, 0)
                                                print(f"      check() returned: {check_result}")
                                        except Exception as e:
                                            print(f"      ✗ Match failed: {e}")
                                            import traceback
                                            traceback.print_exc()
                else:
                    print(f"  ✗ Failed to generate microcode: {hf.str}")
            except Exception as e:
                print(f"  ✗ Error generating microcode: {e}")
                import traceback
                traceback.print_exc()
        else:
            print(f"  ✗ Function not found")
    else:
        print(f"  ✗ test_xor not found in binary")

except Exception as e:
    print(f"✗ Error: {e}")
    import traceback
    traceback.print_exc()
finally:
    # Clean up
    import shutil
    shutil.rmtree(temp_dir, ignore_errors=True)

print("\n" + "=" * 80)
print("DEBUG COMPLETE")
print("=" * 80)
