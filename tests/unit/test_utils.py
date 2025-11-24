import unittest
from unittest.mock import patch, MagicMock

from .tutils import load_conf_classes

# Mock MSB_TABLE to avoid importing ida_hexrays
MSB_TABLE_MOCK = {
    1: 0x80,
    2: 0x8000,
    4: 0x80000000,
    8: 0x8000000000000000,
    16: 0x80000000000000000000000000000000,
}

# Mock the entire hexrays_helpers module
hexrays_helpers_mock = MagicMock()
hexrays_helpers_mock.MSB_TABLE = MSB_TABLE_MOCK

# Use load_conf_classes and patch the module
with load_conf_classes():
    with patch.dict('sys.modules', {'d810.hexrays.hexrays_helpers': hexrays_helpers_mock}):
        from d810.expr.utils import signed_to_unsigned, unsigned_to_signed, get_parity_flag


class TestUtils(unittest.TestCase):
    """Test utility functions for type conversions and bit operations."""

    def test_signed_to_unsigned_small_sizes(self):
        """Test signed_to_unsigned for 1, 2, 4, 8 byte sizes."""
        # Test positive values
        self.assertEqual(signed_to_unsigned(42, 1), 42)
        self.assertEqual(signed_to_unsigned(1000, 2), 1000)
        self.assertEqual(signed_to_unsigned(123456, 4), 123456)
        self.assertEqual(signed_to_unsigned(9876543210, 8), 9876543210)

        # Test negative values (should wrap around)
        self.assertEqual(signed_to_unsigned(-1, 1), 255)  # 0xFF
        self.assertEqual(signed_to_unsigned(-1, 2), 65535)  # 0xFFFF
        self.assertEqual(signed_to_unsigned(-1, 4), 4294967295)  # 0xFFFFFFFF
        self.assertEqual(signed_to_unsigned(-1, 8), 18446744073709551615)  # 0xFFFFFFFFFFFFFFFF

        # Test edge cases
        self.assertEqual(signed_to_unsigned(0, 1), 0)
        self.assertEqual(signed_to_unsigned(127, 1), 127)  # Max positive for int8
        self.assertEqual(signed_to_unsigned(-128, 1), 128)  # Min negative for int8

    def test_unsigned_to_signed_small_sizes(self):
        """Test unsigned_to_signed for 1, 2, 4, 8 byte sizes."""
        # Test positive values
        self.assertEqual(unsigned_to_signed(42, 1), 42)
        self.assertEqual(unsigned_to_signed(1000, 2), 1000)
        self.assertEqual(unsigned_to_signed(123456, 4), 123456)
        self.assertEqual(unsigned_to_signed(9876543210, 8), 9876543210)

        # Test values that should be interpreted as negative
        self.assertEqual(unsigned_to_signed(255, 1), -1)  # 0xFF as signed int8
        self.assertEqual(unsigned_to_signed(65535, 2), -1)  # 0xFFFF as signed int16
        self.assertEqual(unsigned_to_signed(4294967295, 4), -1)  # 0xFFFFFFFF as signed int32
        self.assertEqual(unsigned_to_signed(18446744073709551615, 8), -1)  # 0xFFFFFFFFFFFFFFFF as signed int64

        # Test edge cases
        self.assertEqual(unsigned_to_signed(0, 1), 0)
        self.assertEqual(unsigned_to_signed(127, 1), 127)  # Max positive for int8
        self.assertEqual(unsigned_to_signed(128, 1), -128)  # Min negative for int8

    def test_signed_to_unsigned_16_bytes(self):
        """Test signed_to_unsigned for 16-byte (128-bit) values."""
        # Test positive values
        test_val = 123456789012345678901234567890123456789
        self.assertEqual(signed_to_unsigned(test_val, 16), test_val)

        # Test negative values (should be treated as unsigned 128-bit)
        negative_val = -1
        expected = (1 << 128) - 1  # All bits set for 128-bit unsigned
        self.assertEqual(signed_to_unsigned(negative_val, 16), expected)

        # Test zero
        self.assertEqual(signed_to_unsigned(0, 16), 0)

        # Test large positive value
        large_val = (1 << 127) - 1  # Max positive for signed 128-bit
        self.assertEqual(signed_to_unsigned(large_val, 16), large_val)

    def test_unsigned_to_signed_16_bytes(self):
        """Test unsigned_to_signed for 16-byte (128-bit) values."""
        # Test positive values
        test_val = 123456789012345678901234567890123456789
        self.assertEqual(unsigned_to_signed(test_val, 16), test_val)

        # Test values that should be interpreted as negative (MSB set)
        msb_set = 1 << 127  # Only MSB set in 128-bit value
        expected = msb_set - (1 << 128)  # Sign extension
        self.assertEqual(unsigned_to_signed(msb_set, 16), expected)

        # Test all bits set (should be -1)
        all_bits_set = (1 << 128) - 1
        self.assertEqual(unsigned_to_signed(all_bits_set, 16), -1)

        # Test zero
        self.assertEqual(unsigned_to_signed(0, 16), 0)

    def test_roundtrip_conversion(self):
        """Test that signed->unsigned->signed and unsigned->signed->unsigned roundtrips work."""
        # Test signed -> unsigned -> signed roundtrips
        signed_test_values = [0, 1, -1, 42, -42, 127, -128, -1, 42, -100]

        for val in signed_test_values:
            for size in [1, 2, 4, 8]:
                # signed -> unsigned -> signed
                unsigned = signed_to_unsigned(val, size)
                back_to_signed = unsigned_to_signed(unsigned, size)
                self.assertEqual(back_to_signed, val,
                               f"Signed roundtrip failed for {val} at size {size}: {val} -> {unsigned} -> {back_to_signed}")

        # Test unsigned -> signed -> unsigned roundtrips
        unsigned_test_cases = [
            (0, [1, 2, 4, 8]),
            (1, [1, 2, 4, 8]),
            (42, [1, 2, 4, 8]),
            (127, [1, 2, 4, 8]),
            (255, [1, 2, 4, 8]),  # Max for 1 byte
            (65535, [2, 4, 8]),   # Max for 2 bytes
            (4294967295, [4, 8]), # Max for 4 bytes
        ]

        for val, sizes in unsigned_test_cases:
            for size in sizes:
                # unsigned -> signed -> unsigned
                signed = unsigned_to_signed(val, size)
                back_to_unsigned = signed_to_unsigned(signed, size)
                self.assertEqual(back_to_unsigned, val,
                               f"Unsigned roundtrip failed for {val} at size {size}: {val} -> {signed} -> {back_to_unsigned}")

    def test_get_parity_flag(self):
        """Test get_parity_flag function."""
        # The function returns 1 when number of 1 bits is even, 0 when odd
        # Test cases with even number of 1s (should return 1)
        self.assertEqual(get_parity_flag(1, 2, 4), 1)  # 1-2 = -1, 32 ones (even)
        self.assertEqual(get_parity_flag(4, 4, 4), 1)  # 4-4 = 0, 0 ones (even)
        self.assertEqual(get_parity_flag(3, 0, 1), 1)  # 3 in 8 bits: 11 (2 ones, even)

        # Test cases with odd number of 1s (should return 0)
        self.assertEqual(get_parity_flag(1, 0, 4), 0)  # 1-0 = 1, 1 one (odd)
        self.assertEqual(get_parity_flag(7, 2, 4), 1)  # 7-2 = 5, binary: 101 (2 ones, even)
        self.assertEqual(get_parity_flag(1, 0, 1), 0)  # 1 in 8 bits: 1 one (odd)

        # Test 16-byte case
        self.assertEqual(get_parity_flag(1, 0, 16), 0)  # 1 in 128 bits: odd parity
        self.assertEqual(get_parity_flag(3, 0, 16), 1)  # 3 in 128 bits: even parity

    def test_large_values_16_bytes(self):
        """Test handling of very large values for 16-byte operations."""
        # Test maximum 128-bit unsigned value
        max_u128 = (1 << 128) - 1
        self.assertEqual(signed_to_unsigned(max_u128, 16), max_u128)
        self.assertEqual(unsigned_to_signed(max_u128, 16), -1)  # All bits set = -1

        # Test maximum 128-bit signed value
        max_s128 = (1 << 127) - 1
        self.assertEqual(unsigned_to_signed(max_s128, 16), max_s128)

        # Test minimum 128-bit signed value
        min_s128 = -(1 << 127)
        self.assertEqual(signed_to_unsigned(min_s128, 16), 1 << 127)

    def test_invalid_sizes(self):
        """Test behavior with unsupported byte sizes."""
        with self.assertRaises(KeyError):
            signed_to_unsigned(42, 3)  # 3 bytes not supported

        with self.assertRaises(KeyError):
            unsigned_to_signed(42, 32)  # 32 bytes not supported

        with self.assertRaises(KeyError):
            get_parity_flag(1, 2, 64)  # 64 bytes not supported


if __name__ == "__main__":
    unittest.main()
