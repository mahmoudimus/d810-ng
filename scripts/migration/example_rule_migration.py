"""Example of migrating a rule to use the new constraint syntax.

This demonstrates how PredSetnz_1 could be written with declarative constraints.
"""

from d810.optimizers.dsl import Var, Const

# Define variables
x = Var("x_0")
c1 = Const("c_1")
c2 = Const("c_2")

print("=" * 70)
print("Example: Migrating PredSetnz_1")
print("=" * 70)

print("\n--- CURRENT (can't be verified) ---")
print("""
class PredSetnz_1(VerifiableRule):
    '''Simplify: (x | c1) != c2 => 1 (when c1 | c2 != c2)'''

    c1, c2 = Const("c_1"), Const("c_2")

    PATTERN = x | c1  # c2 is missing - added by framework
    REPLACEMENT = ONE

    CONSTRAINTS = [
        lambda ctx: (ctx["c_1"].value | ctx["c_2"].value) != ctx["c_2"].value
    ]

    # Can't verify with Z3 because c2 not in PATTERN
    SKIP_VERIFICATION = True
""")

print("\n--- NEW DECLARATIVE STYLE ---")
print("""
class PredSetnz_1_New(VerifiableRule):
    '''Simplify: (x | c1) != c2 => 1 (when c1 | c2 != c2)'''

    c1, c2 = Const("c_1"), Const("c_2")

    PATTERN = x | c1
    REPLACEMENT = ONE

    # Natural Python syntax - reads like the mathematical condition!
    CONSTRAINTS = [(c1 | c2) != c2]

    # Still can't fully verify because c2 not in pattern,
    # but the constraint itself is now declarative
""")

# Create the actual constraint
constraint = (c1 | c2) != c2

print("\n--- Testing the Constraint ---")
print(f"Constraint: {constraint}")
print(f"Type: {type(constraint)}")

# Test with concrete values
class MockMop:
    def __init__(self, val):
        self.value = val

test_cases = [
    {"c_1": MockMop(0b1010), "c_2": MockMop(0b0010)},  # (1010 | 0010) != 0010 => 1010 != 0010 => True
    {"c_1": MockMop(0b0001), "c_2": MockMop(0b0011)},  # (0001 | 0011) != 0011 => 0011 != 0011 => False
    {"c_1": MockMop(0xFF), "c_2": MockMop(0x00)},      # (FF | 00) != 00 => FF != 00 => True
]

print("\nTest Cases:")
for i, ctx in enumerate(test_cases, 1):
    result = constraint(ctx)  # Using __call__ for backward compat
    c1_val = ctx["c_1"].value
    c2_val = ctx["c_2"].value
    expected = (c1_val | c2_val) != c2_val
    status = "✓" if result == expected else "✗"
    print(f"  {status} Case {i}: c1={c1_val:04x}, c2={c2_val:04x} => {result} (expected {expected})")

print("\n--- Benefits of New Syntax ---")
print("  ✓ Reads like mathematics: (c1 | c2) != c2")
print("  ✓ No manual ctx[] lookups")
print("  ✓ No .value attribute access")
print("  ✓ Type-checked at constraint creation time")
print("  ✓ Can compose with & | ~ for complex logic")
print("  ✓ Automatic Z3 conversion (when all variables in pattern)")

print("\n--- More Complex Example ---")
# Example showing composition
complex_constraint = ((c1 | c2) != c2) & (c1 > Const("0", 0))
print(f"Complex: {complex_constraint}")
print("Type: AndConstraint with two sub-constraints")

print("\n" + "=" * 70)
print("Migration Complete!")
print("=" * 70)
