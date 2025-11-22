"""Platform-independent opcode definitions for d810.

This module defines opcode constants that are independent of IDA Pro.
These opcodes are used for:
- Declarative DSL pattern matching
- Z3 symbolic verification
- AST representation

The actual integer values are arbitrary - only uniqueness matters.
When interfacing with IDA Pro, these opcodes are mapped to IDA's opcodes.
"""

# Arithmetic operations
M_ADD = 0
M_SUB = 1
M_MUL = 2
M_UDIV = 3
M_SDIV = 4
M_UMOD = 5
M_SMOD = 6
M_NEG = 7

# Bitwise operations
M_AND = 8
M_OR = 9
M_XOR = 10
M_BNOT = 11
M_SHL = 12
M_SHR = 13
M_SAR = 14

# Logical operations
M_LNOT = 15

# Comparison operations
M_SETZ = 16
M_SETNZ = 17
M_SETAE = 18
M_SETA = 19
M_SETB = 20
M_SETBE = 21
M_SETG = 22
M_SETGE = 23
M_SETL = 24
M_SETLE = 25
M_SETP = 26
M_SETS = 27

# Extension operations
M_XDU = 28
M_XDS = 29
M_LOW = 30
M_HIGH = 31

# Movement and special
M_MOV = 32
M_NOP = 33

# Memory operations
M_STX = 34
M_LDX = 35
M_LDC = 36

# Control flow
M_JCND = 37
M_JNZ = 38
M_JZ = 39
M_JAE = 40
M_JA = 41
M_JB = 42
M_JBE = 43
M_JG = 44
M_JGE = 45
M_JL = 46
M_JLE = 47
M_JTBL = 48
M_IJMP = 49
M_GOTO = 50

# Function calls
M_CALL = 51
M_ICALL = 52
M_RET = 53

# Stack operations
M_PUSH = 54
M_POP = 55

# Flag operations
M_CFADD = 56
M_OFADD = 57
M_CFSHL = 58
M_CFSHR = 59
M_SETO = 60

# Floating point
M_F2I = 61
M_F2U = 62
M_I2F = 63
M_U2F = 64
M_F2F = 65
M_FNEG = 66
M_FADD = 67
M_FSUB = 68
M_FMUL = 69
M_FDIV = 70

# Other
M_UND = 71
M_EXT = 72


# Opcode metadata (independent of IDA)
OPCODES_INFO = {
    M_NOP: {"name": "nop", "nb_operands": 0, "is_commutative": True},
    M_STX: {"name": "stx", "nb_operands": 2, "is_commutative": False},
    M_LDX: {"name": "ldx", "nb_operands": 2, "is_commutative": False},
    M_LDC: {"name": "ldc", "nb_operands": 1, "is_commutative": False},
    M_MOV: {"name": "mov", "nb_operands": 1, "is_commutative": False, "symbol": ""},
    M_NEG: {"name": "neg", "nb_operands": 1, "is_commutative": False, "symbol": "-"},
    M_LNOT: {"name": "lnot", "nb_operands": 1, "is_commutative": False, "symbol": "!"},
    M_BNOT: {"name": "bnot", "nb_operands": 1, "is_commutative": False, "symbol": "~"},
    M_XDS: {"name": "xds", "nb_operands": 1, "is_commutative": False, "symbol": "xds"},
    M_XDU: {"name": "xdu", "nb_operands": 1, "is_commutative": False, "symbol": "xdu"},
    M_LOW: {"name": "low", "nb_operands": 1, "is_commutative": False, "symbol": "low"},
    M_HIGH: {"name": "high", "nb_operands": 1, "is_commutative": False, "symbol": "high"},
    M_ADD: {"name": "add", "nb_operands": 2, "is_commutative": True, "symbol": "+"},
    M_SUB: {"name": "sub", "nb_operands": 2, "is_commutative": False, "symbol": "-"},
    M_MUL: {"name": "mul", "nb_operands": 2, "is_commutative": True, "symbol": "*"},
    M_UDIV: {"name": "udiv", "nb_operands": 2, "is_commutative": False, "symbol": "UDiv"},
    M_SDIV: {"name": "sdiv", "nb_operands": 2, "is_commutative": False, "symbol": "/"},
    M_UMOD: {"name": "umod", "nb_operands": 2, "is_commutative": False, "symbol": "URem"},
    M_SMOD: {"name": "smod", "nb_operands": 2, "is_commutative": False, "symbol": "%"},
    M_OR: {"name": "or", "nb_operands": 2, "is_commutative": True, "symbol": "|"},
    M_AND: {"name": "and", "nb_operands": 2, "is_commutative": True, "symbol": "&"},
    M_XOR: {"name": "xor", "nb_operands": 2, "is_commutative": True, "symbol": "^"},
    M_SHL: {"name": "shl", "nb_operands": 2, "is_commutative": False, "symbol": "<<"},
    M_SHR: {"name": "shr", "nb_operands": 2, "is_commutative": False, "symbol": "LShR"},
    M_SAR: {"name": "sar", "nb_operands": 2, "is_commutative": False, "symbol": ">>"},
    M_CFADD: {"name": "cfadd", "nb_operands": 2, "is_commutative": True},
    M_OFADD: {"name": "ofadd", "nb_operands": 2, "is_commutative": True},
    M_CFSHL: {"name": "cfshl", "nb_operands": 2, "is_commutative": False},
    M_CFSHR: {"name": "cfshr", "nb_operands": 2, "is_commutative": False},
    M_SETS: {"name": "sets", "nb_operands": 2, "is_commutative": False},
    M_SETO: {"name": "seto", "nb_operands": 2, "is_commutative": False},
    M_SETP: {"name": "setp", "nb_operands": 2, "is_commutative": False},
    M_SETNZ: {"name": "setnz", "nb_operands": 2, "is_commutative": True, "symbol": "!="},
    M_SETZ: {"name": "setz", "nb_operands": 2, "is_commutative": True, "symbol": "=="},
    M_SETA: {"name": "seta", "nb_operands": 2, "is_commutative": False, "symbol": ">"},
    M_SETAE: {"name": "setae", "nb_operands": 2, "is_commutative": False, "symbol": ">="},
    M_SETB: {"name": "setb", "nb_operands": 2, "is_commutative": False, "symbol": "<"},
    M_SETBE: {"name": "setbe", "nb_operands": 2, "is_commutative": False, "symbol": "<="},
    M_SETG: {"name": "setg", "nb_operands": 2, "is_commutative": False, "symbol": "UGT"},
    M_SETGE: {"name": "setge", "nb_operands": 2, "is_commutative": False, "symbol": "UGE"},
    M_SETL: {"name": "setl", "nb_operands": 2, "is_commutative": False, "symbol": "ULT"},
    M_SETLE: {"name": "setle", "nb_operands": 2, "is_commutative": False, "symbol": "ULE"},
    M_JCND: {"name": "jcnd", "nb_operands": 1, "is_commutative": False},
    M_JNZ: {"name": "jnz", "nb_operands": 2, "is_commutative": True},
    M_JZ: {"name": "jz", "nb_operands": 2, "is_commutative": True},
    M_JAE: {"name": "jae", "nb_operands": 2, "is_commutative": False},
    M_JB: {"name": "jb", "nb_operands": 2, "is_commutative": False},
    M_JA: {"name": "ja", "nb_operands": 2, "is_commutative": False},
    M_JBE: {"name": "jbe", "nb_operands": 2, "is_commutative": False},
    M_JG: {"name": "jg", "nb_operands": 2, "is_commutative": False},
    M_JGE: {"name": "jge", "nb_operands": 2, "is_commutative": False},
    M_JL: {"name": "jl", "nb_operands": 2, "is_commutative": False},
    M_JLE: {"name": "jle", "nb_operands": 2, "is_commutative": False},
    M_JTBL: {"name": "jtbl", "nb_operands": 2, "is_commutative": False},
    M_IJMP: {"name": "ijmp", "nb_operands": 2, "is_commutative": False},
    M_GOTO: {"name": "goto", "nb_operands": 1, "is_commutative": False},
    M_CALL: {"name": "call", "nb_operands": 2, "is_commutative": False},
    M_ICALL: {"name": "icall", "nb_operands": 2, "is_commutative": False},
    M_RET: {"name": "ret", "nb_operands": 0, "is_commutative": False},
    M_PUSH: {"name": "push", "nb_operands": 0, "is_commutative": False},
    M_POP: {"name": "pop", "nb_operands": 0, "is_commutative": False},
    M_UND: {"name": "und", "nb_operands": 0, "is_commutative": False},
    M_EXT: {"name": "ext", "nb_operands": 0, "is_commutative": False},
    M_F2I: {"name": "f2i", "nb_operands": 2, "is_commutative": False},
    M_F2U: {"name": "f2u", "nb_operands": 2, "is_commutative": False},
    M_I2F: {"name": "i2f", "nb_operands": 2, "is_commutative": False},
    M_U2F: {"name": "u2f", "nb_operands": 2, "is_commutative": False},
    M_F2F: {"name": "f2f", "nb_operands": 2, "is_commutative": False},
    M_FNEG: {"name": "fneg", "nb_operands": 2, "is_commutative": False},
    M_FADD: {"name": "fadd", "nb_operands": 2, "is_commutative": True},
    M_FSUB: {"name": "fsub", "nb_operands": 2, "is_commutative": False},
    M_FMUL: {"name": "fmul", "nb_operands": 2, "is_commutative": True},
    M_FDIV: {"name": "fdiv", "nb_operands": 2, "is_commutative": False},
}


def ida_to_d810_opcode(ida_opcode: int) -> int:
    """Convert IDA opcode to d810 opcode.

    This function is called when interfacing with IDA Pro to translate
    IDA's opcodes to our platform-independent opcodes.

    Args:
        ida_opcode: IDA Pro opcode constant (e.g., ida_hexrays.m_add)

    Returns:
        Corresponding d810 opcode constant (e.g., M_ADD)
    """
    # Import IDA modules only when this function is called (lazy import)
    try:
        import ida_hexrays

        # Map IDA opcodes to d810 opcodes
        IDA_TO_D810_MAP = {
            ida_hexrays.m_add: M_ADD,
            ida_hexrays.m_sub: M_SUB,
            ida_hexrays.m_mul: M_MUL,
            ida_hexrays.m_udiv: M_UDIV,
            ida_hexrays.m_sdiv: M_SDIV,
            ida_hexrays.m_umod: M_UMOD,
            ida_hexrays.m_smod: M_SMOD,
            ida_hexrays.m_neg: M_NEG,
            ida_hexrays.m_and: M_AND,
            ida_hexrays.m_or: M_OR,
            ida_hexrays.m_xor: M_XOR,
            ida_hexrays.m_bnot: M_BNOT,
            ida_hexrays.m_shl: M_SHL,
            ida_hexrays.m_shr: M_SHR,
            ida_hexrays.m_sar: M_SAR,
            ida_hexrays.m_lnot: M_LNOT,
            # Add more mappings as needed
        }

        return IDA_TO_D810_MAP.get(ida_opcode, ida_opcode)
    except ImportError:
        # If IDA is not available, assume the opcode is already a d810 opcode
        return ida_opcode


def d810_to_ida_opcode(d810_opcode: int) -> int:
    """Convert d810 opcode to IDA opcode.

    This function is called when interfacing with IDA Pro to translate
    our platform-independent opcodes to IDA's opcodes.

    Args:
        d810_opcode: d810 opcode constant (e.g., M_ADD)

    Returns:
        Corresponding IDA Pro opcode constant (e.g., ida_hexrays.m_add)
    """
    # Import IDA modules only when this function is called (lazy import)
    try:
        import ida_hexrays

        # Map d810 opcodes to IDA opcodes
        D810_TO_IDA_MAP = {
            M_ADD: ida_hexrays.m_add,
            M_SUB: ida_hexrays.m_sub,
            M_MUL: ida_hexrays.m_mul,
            M_UDIV: ida_hexrays.m_udiv,
            M_SDIV: ida_hexrays.m_sdiv,
            M_UMOD: ida_hexrays.m_umod,
            M_SMOD: ida_hexrays.m_smod,
            M_NEG: ida_hexrays.m_neg,
            M_AND: ida_hexrays.m_and,
            M_OR: ida_hexrays.m_or,
            M_XOR: ida_hexrays.m_xor,
            M_BNOT: ida_hexrays.m_bnot,
            M_SHL: ida_hexrays.m_shl,
            M_SHR: ida_hexrays.m_shr,
            M_SAR: ida_hexrays.m_sar,
            M_LNOT: ida_hexrays.m_lnot,
            # Add more mappings as needed
        }

        return D810_TO_IDA_MAP.get(d810_opcode, d810_opcode)
    except ImportError:
        # If IDA is not available, return as-is (will fail later if actually used)
        return d810_opcode
