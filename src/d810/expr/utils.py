import ctypes

from d810.cache import CacheImpl
from d810.hexrays.hexrays_helpers import MSB_TABLE
from d810.registry import survives_reload

CTYPE_SIGNED_TABLE = {
    1: ctypes.c_int8,
    2: ctypes.c_int16,
    4: ctypes.c_int32,
    8: ctypes.c_int64,
    16: ctypes.c_ubyte * 16,
}
CTYPE_UNSIGNED_TABLE = {
    1: ctypes.c_uint8,
    2: ctypes.c_uint16,
    4: ctypes.c_uint32,
    8: ctypes.c_uint64,
    16: ctypes.c_ubyte * 16,
}


def get_all_subclasses(python_class):
    python_class.__subclasses__()

    subclasses = set()
    check_these = [python_class]

    while check_these:
        parent = check_these.pop()
        for child in parent.__subclasses__():
            if child not in subclasses:
                subclasses.add(child)
                check_these.append(child)

    return sorted(subclasses, key=lambda x: x.__name__)


def unsigned_to_signed(unsigned_value, nb_bytes):
    ctype_class = CTYPE_SIGNED_TABLE[nb_bytes]
    if nb_bytes == 16:
        # For 128-bit values, convert to bytes and back as signed
        byte_array = ctype_class()
        for i in range(16):
            byte_array[i] = (unsigned_value >> (i * 8)) & 0xFF
        # Convert back to int, treating as signed
        result = 0
        for i in range(16):
            result |= byte_array[i] << (i * 8)
        # Apply sign extension if MSB is set
        if result & (1 << 127):
            result |= ~((1 << 128) - 1)
        return result
    else:
        return ctype_class(unsigned_value).value


def signed_to_unsigned(signed_value, nb_bytes):
    ctype_class = CTYPE_UNSIGNED_TABLE[nb_bytes]
    if nb_bytes == 16:
        # For 128-bit values, convert to bytes and back as unsigned
        byte_array = ctype_class()
        for i in range(16):
            byte_array[i] = (signed_value >> (i * 8)) & 0xFF
        # Convert back to int as unsigned
        result = 0
        for i in range(16):
            result |= byte_array[i] << (i * 8)
        return result & ((1 << 128) - 1)
    else:
        return ctype_class(signed_value).value


def get_msb(value, nb_bytes):
    return (value & MSB_TABLE[nb_bytes]) >> (nb_bytes * 8 - 1)


def get_add_cf(op1, op2, nb_bytes):
    res = op1 + op2
    return get_msb((((op1 ^ op2) ^ res) ^ ((op1 ^ res) & (~(op1 ^ op2)))), nb_bytes)


def get_add_of(op1, op2, nb_bytes):
    res = op1 + op2
    return get_msb(((op1 ^ res) & (~(op1 ^ op2))), nb_bytes)


def get_sub_cf(op1, op2, nb_bytes):
    res = op1 - op2
    return get_msb((((op1 ^ op2) ^ res) ^ ((op1 ^ res) & (op1 ^ op2))), nb_bytes)


def get_sub_of(op1, op2, nb_bytes):
    res = op1 - op2
    return get_msb(((op1 ^ res) & (op1 ^ op2)), nb_bytes)


def get_parity_flag(op1, op2, nb_bytes):
    if nb_bytes == 16:
        tmp = signed_to_unsigned(op1 - op2, nb_bytes)
    else:
        tmp = CTYPE_UNSIGNED_TABLE[nb_bytes](op1 - op2).value
    return (bin(tmp).count("1") + 1) % 2


def ror(x, n, nb_bits=32):
    mask = (2**n) - 1
    mask_bits = x & mask
    return (x >> n) | (mask_bits << (nb_bits - n))


def rol(x, n, nb_bits=32):
    return ror(x, nb_bits - n, nb_bits)


def __rol__(value: int, count: int, bits: int) -> int:
    """
    Rotate left on an unsigned integer of given bit width.
    """
    mask = (1 << bits) - 1
    count %= bits
    value &= mask
    return ((value << count) & mask) | (value >> (bits - count))


def __ror__(value: int, count: int, bits: int) -> int:
    """
    Rotate right on an unsigned integer of given bit width.
    """
    return __rol__(value, -count, bits)


def __ROL1__(value: int, count: int) -> int:
    return __rol__(value, count, 8)


def __ROL2__(value: int, count: int) -> int:
    return __rol__(value, count, 16)


def __ROL4__(value: int, count: int) -> int:
    return __rol__(value, count, 32)


def __ROL8__(value: int, count: int) -> int:
    return __rol__(value, count, 64)


def __ROR1__(value: int, count: int) -> int:
    return __ror__(value, count, 8)


def __ROR2__(value: int, count: int) -> int:
    return __ror__(value, count, 16)


def __ROR4__(value: int, count: int) -> int:
    return __ror__(value, count, 32)


def __ROR8__(value: int, count: int) -> int:
    return __ror__(value, count, 64)


@survives_reload(reload_key="_SHARED_MOP_CACHES")
class _SharedMopCaches:
    """
    Holds the global mop caches and survives module reloads so every
    importer (Python or Cython) sees the same instances.
    """

    def __init__(self) -> None:
        # Keep sizes reasonable; tweak as needed elsewhere.
        self.MOP_CONSTANT_CACHE = CacheImpl(max_size=1000)
        self.MOP_TO_AST_CACHE = CacheImpl(max_size=20480)


_shared_caches = _SharedMopCaches()

# Public module-level aliases used throughout the codebase (and Cython)
MOP_CONSTANT_CACHE = _shared_caches.MOP_CONSTANT_CACHE

MOP_TO_AST_CACHE = _shared_caches.MOP_TO_AST_CACHE
