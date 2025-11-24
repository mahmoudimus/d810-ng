"""Constants for MBA (Mixed Boolean-Arithmetic) operations.

This module contains pure Python constants used in MBA simplification
and pattern matching. No IDA dependencies.
"""

# Subtraction modulo lookup table for different bit widths
# Used in rules that need to know the modulus for a given bit width
# Example: For 8-bit (1 byte), modulus is 0x100 (256)
SUB_TABLE: dict[int, int] = {
    1: 0x100,                                    # 8-bit:  2^8  = 256
    2: 0x10000,                                  # 16-bit: 2^16 = 65536
    4: 0x100000000,                              # 32-bit: 2^32
    8: 0x10000000000000000,                      # 64-bit: 2^64
    16: 0x100000000000000000000000000000000,    # 128-bit: 2^128
}

# All-ones mask (bitwise NOT mask) for different bit widths
# XORing with an all-ones mask is equivalent to bitwise NOT (~)
# Example: For 8-bit, mask is 0xFF (all bits set)
AND_TABLE: dict[int, int] = {
    1: 0xFF,                                     # 8-bit:  all ones
    2: 0xFFFF,                                   # 16-bit: all ones
    4: 0xFFFFFFFF,                               # 32-bit: all ones
    8: 0xFFFFFFFFFFFFFFFF,                       # 64-bit: all ones
    16: 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,     # 128-bit: all ones
}

__all__ = ["SUB_TABLE", "AND_TABLE"]
