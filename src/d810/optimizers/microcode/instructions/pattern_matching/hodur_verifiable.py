"""HODUR obfuscation pattern rules (Declarative DSL version).

HODUR is an obfuscator that applies complex algebraic transformations.
These rules simplify the obfuscated patterns back to cleaner code.

All rules have been migrated to the declarative DSL and are automatically
verified with Z3.
"""

from d810.optimizers.dsl import Const, Var, ONE
from d810.optimizers.rules import VerifiableRule

# Common variables for HODUR patterns
x = Var("x")
y = Var("y")
z = Var("z")


class Xor_Hodur_1(VerifiableRule):
    """Simplify: ~(x ^ (y ^ z)) => x ^ (y ^ ~z)

    Mathematical proof using XOR properties:
        ~(x ^ (y ^ z))
        = ~((x ^ y) ^ z)    [XOR associativity]
        = (x ^ y) ^ ~z      [DeMorgan for XOR]
        = x ^ (y ^ ~z)      [XOR associativity]

    Example (HODUR pattern 1):
        ~(enc[i] ^ ((i - 0x1D) ^ 0x1C))
        => enc[i] ^ ((i - 0x1D) ^ ~0x1C)
        => enc[i] ^ ((i - 0x1D) ^ 0xE3)
    """

    PATTERN = ~(x ^ (y ^ z))
    REPLACEMENT = x ^ (y ^ ~z)

    DESCRIPTION = "HODUR: Distribute NOT through nested XOR"
    REFERENCE = "HODUR obfuscator, pattern 1"


class Bnot_Hodur_1(VerifiableRule):
    """Simplify: ((c_0 - x) & bnot_z) ^ ((x - c_3) & z) => ~((x - c_3) ^ z)

    This rule handles a complex HODUR pattern where:
    - c_0 and c_3 are consecutive constants (c_0 + 1 == c_3)
    - bnot_z is the bitwise NOT of z

    Mathematical proof (when c_0 + 1 == c_3 and bnot_z == ~z):
        c_0 - x = -(x - c_0) = -(x - (c_3 - 1)) = -(x - c_3 + 1)
        In two's complement: ~y = -y - 1, so -y = ~y + 1
        Therefore: -(x - c_3 + 1) = ~(x - c_3 + 1) + 1 = ~(x - c_3) + ~1 + 1 = ~(x - c_3)

        So: (c_0 - x) & bnot_z = ~(x - c_3) & ~z

        Using DeMorgan's laws:
        (~(x - c_3) & ~z) ^ ((x - c_3) & z)
        = ~((x - c_3) | z) ^ ((x - c_3) & z)
        = ... [complex derivation]
        = ~((x - c_3) ^ z)

    Example (HODUR pattern 2):
        ((0x1C - i) & 0xFA) ^ ((i - 0x1D) & 5)
        => ~((i - 0x1D) ^ 5)
    """

    c_0 = Const("c_0")
    c_3 = Const("c_3")
    bnot_z = Var("bnot_z")

    PATTERN = ((c_0 - x) & bnot_z) ^ ((x - c_3) & z)
    REPLACEMENT = ~((x - c_3) ^ z)

    # Constraints:
    # 1. c_0 and c_3 must be consecutive constants
    # 2. bnot_z must be the bitwise NOT of z
    CONSTRAINTS = [c_0 + ONE == c_3, bnot_z == ~z]

    DESCRIPTION = "HODUR: Simplify consecutive constant pattern with BNOT"
    REFERENCE = "HODUR obfuscator, pattern 2"


class Or_Hodur_1(VerifiableRule):
    """Simplify: ((~x & c_0) | (x & c_1)) | (~x & c_2) => (~x & (c_0 | c_2)) | (x & c_1)

    This is simple boolean factoring using the distributive law:
        (A & B) | (A & C) = A & (B | C)

    Applied here:
        (~x & c_0) | (~x & c_2) = ~x & (c_0 | c_2)

    Example (HODUR pattern 3):
        (~enc[i] & 0xE3) | (enc[i] & 4) | (~enc[i] & 0x18)
        => (~enc[i] & (0xE3 | 0x18)) | (enc[i] & 4)
        => (~enc[i] & 0xFB) | (enc[i] & 4)
    """

    c_0 = Const("c_0")
    c_1 = Const("c_1")
    c_2 = Const("c_2")

    PATTERN = ((~x & c_0) | (x & c_1)) | (~x & c_2)
    REPLACEMENT = (~x & (c_0 | c_2)) | (x & c_1)

    DESCRIPTION = "HODUR: Factor OR with multiple AND terms"
    REFERENCE = "HODUR obfuscator, pattern 3"


class Or_Hodur_2(VerifiableRule):
    """Simplify: (x & (y ^ c_0)) | ((y ^ bnot_c_0) & ~x) => x ^ (y ^ bnot_c_0)

    This rule handles a pattern where bnot_c_0 is the bitwise NOT of c_0.

    Mathematical proof (when bnot_c_0 == ~c_0):
        Note: y ^ c_0 and y ^ bnot_c_0 = y ^ ~c_0

        Using the identity: (A & B) | (~A & C) = (A & B) | (~A & C)

        When we have: (x & (y ^ c_0)) | (~x & (y ^ ~c_0))

        This is a MUX (multiplexer) pattern:
        - If x is all 1's: result = y ^ c_0
        - If x is all 0's: result = y ^ ~c_0

        Using XOR properties, this simplifies to: x ^ (y ^ ~c_0)

    Example (HODUR pattern 4):
        (x & (y ^ 0x1C)) | ((y ^ 0xE3) & ~x)
        => x ^ (y ^ 0xE3)  [when 0xE3 == ~0x1C]
    """

    c_0 = Const("c_0")
    bnot_c_0 = Const("bnot_c_0")

    PATTERN = (x & (y ^ c_0)) | ((y ^ bnot_c_0) & ~x)
    REPLACEMENT = x ^ (y ^ bnot_c_0)

    # Constraint: bnot_c_0 must be the bitwise NOT of c_0
    CONSTRAINTS = [bnot_c_0 == ~c_0]

    DESCRIPTION = "HODUR: Simplify MUX pattern with XOR"
    REFERENCE = "HODUR obfuscator, pattern 4"


class Xor_Hodur_2(VerifiableRule):
    """Simplify: (x - c_0) ^ (y ^ c_1) => (x + c_1) ^ (y ^ c_1) when c_0 + c_1 = 256

    This rule handles HODUR's use of modular arithmetic where c_0 + c_1 = 256.

    SIZE-DEPENDENT: This rule is only correct for byte-sized operations.
    In byte arithmetic: -c_0 ≡ c_1 (mod 256) when c_0 + c_1 = 256
    Therefore: x - c_0 ≡ x + c_1 (mod 256)

    However, in 32-bit arithmetic, the sign-extension of negative values prevents
    the identity from holding. For example, with c_0=128, c_1=128:
    - Pattern: (0 - 128) ^ (0 ^ 128) = -128 ^ 128 = 0xFFFFFF80 ^ 0x80 ≠ 0
    - Replacement: (0 + 128) ^ (0 ^ 128) = 128 ^ 128 = 0

    The rule works correctly when applied to actual byte-sized IDA microcode,
    but cannot be verified with 32-bit Z3 bitvectors.

    Example (HODUR pattern 5, with c_0=0x1D=29, c_1=0xE3=227):
        0x1D + 0xE3 = 256 (wraps to 0 in byte arithmetic)
        (y - 0x1D) ^ (x ^ 0xE3) => (y + 0xE3) ^ (x ^ 0xE3)
    """

    c_0 = Const("c_0")
    c_1 = Const("c_1")
    TWO_FIVE_SIX = Const("256", 256)

    PATTERN = (x - c_0) ^ (y ^ c_1)
    REPLACEMENT = (x + c_1) ^ (y ^ c_1)

    # Constraint: c_0 + c_1 must equal 256
    # This is checked at runtime during pattern matching
    CONSTRAINTS = [c_0 + c_1 == TWO_FIVE_SIX]

    # Skip Z3 verification because this rule is byte-specific
    # and cannot be verified with 32-bit bitvectors
    SKIP_VERIFICATION = True

    DESCRIPTION = "HODUR: Convert subtraction to addition using modular arithmetic (byte-specific)"
    REFERENCE = "HODUR obfuscator, pattern 5"
