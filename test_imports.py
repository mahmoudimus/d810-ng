#!/usr/bin/env python3
"""Test script to verify refactored modules can be imported."""

import sys

def test_import(module_name):
    """Test if a module can be imported."""
    try:
        __import__(module_name)
        print(f"✓ {module_name}")
        return True
    except Exception as e:
        print(f"✗ {module_name}: {e}")
        return False

print("Testing infrastructure imports...")
modules_to_test = [
    "d810.optimizers.dsl",
    "d810.optimizers.core",
    "d810.optimizers.rules",
    "d810.optimizers.instrumentation",
    "d810.optimizers.caching",
    "d810.optimizers.profiling",
    "d810.optimizers.parallel",
    "d810.optimizers.manager",
]

success_count = 0
for mod in modules_to_test:
    if test_import(mod):
        success_count += 1

print(f"\nInfrastructure: {success_count}/{len(modules_to_test)} modules imported successfully")

print("\nTesting refactored pattern matching rules...")
refactored_rules = [
    "d810.optimizers.microcode.instructions.pattern_matching.rewrite_xor_refactored",
    "d810.optimizers.microcode.instructions.pattern_matching.rewrite_and_refactored",
    "d810.optimizers.microcode.instructions.pattern_matching.rewrite_or_refactored",
    "d810.optimizers.microcode.instructions.pattern_matching.rewrite_add_refactored",
    "d810.optimizers.microcode.instructions.pattern_matching.rewrite_sub_refactored",
    "d810.optimizers.microcode.instructions.pattern_matching.rewrite_mul_refactored",
    "d810.optimizers.microcode.instructions.pattern_matching.rewrite_neg_refactored",
    "d810.optimizers.microcode.instructions.pattern_matching.rewrite_bnot_refactored",
    "d810.optimizers.microcode.instructions.pattern_matching.rewrite_cst_refactored",
    "d810.optimizers.microcode.instructions.pattern_matching.rewrite_mov_refactored",
    "d810.optimizers.microcode.instructions.pattern_matching.rewrite_predicates_refactored",
]

success_count = 0
for mod in refactored_rules:
    if test_import(mod):
        success_count += 1

print(f"\nRefactored rules: {success_count}/{len(refactored_rules)} modules imported successfully")

print("\nChecking if rules are registered...")
try:
    from d810.optimizers.microcode.instructions.handler import InstructionOptimizationRule
    print(f"Total rules in InstructionOptimizationRule.registry: {len(InstructionOptimizationRule.registry)}")

    # Check for refactored rules
    refactored_in_registry = [name for name in InstructionOptimizationRule.registry.keys()
                               if "refactored" in name.lower() or "hackersdelight" in name.lower() or "mba" in name.lower()]
    print(f"Refactored/DSL rules found: {len(refactored_in_registry)}")
    if refactored_in_registry[:10]:
        print("Sample refactored rules:")
        for name in refactored_in_registry[:10]:
            print(f"  - {name}")

except Exception as e:
    print(f"Error checking registry: {e}")

print("\nChecking VerifiableRule registry...")
try:
    from d810.optimizers.rules import RULE_REGISTRY
    print(f"Total rules in RULE_REGISTRY: {len(RULE_REGISTRY)}")
    if RULE_REGISTRY[:5]:
        print("Sample rules:")
        for rule in RULE_REGISTRY[:5]:
            print(f"  - {rule.__class__.__name__}")
except Exception as e:
    print(f"Error checking VerifiableRule registry: {e}")
