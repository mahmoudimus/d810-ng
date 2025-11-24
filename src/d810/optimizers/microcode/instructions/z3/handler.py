import abc

import ida_hexrays

from d810.expr.ast import AstNode
from d810.optimizers.microcode.instructions.handler import (
    GenericPatternRule,
    InstructionOptimizer,
)


class Z3Rule(GenericPatternRule):

    @property
    @abc.abstractmethod
    def PATTERN(self) -> AstNode:
        """Return the pattern to match."""

    @property
    @abc.abstractmethod
    def REPLACEMENT_PATTERN(self) -> AstNode:
        """Return the replacement pattern."""


class Z3Optimizer(InstructionOptimizer):
    RULE_CLASSES = [Z3Rule]

    def __init__(self, maturities, stats, log_dir=None):
        super().__init__(maturities, stats, log_dir)
        self._allowed_root_opcodes: set[int] = set()

    def add_rule(self, rule: Z3Rule) -> bool:  # type: ignore[override]
        ok = super().add_rule(rule)
        if not ok:
            return False
        try:
            pat = rule.PATTERN
            if isinstance(pat, AstNode) and pat.opcode is not None:
                self._allowed_root_opcodes.add(int(pat.opcode))
        except Exception:
            pass
        return True

    def get_optimized_instruction(self, blk: ida_hexrays.mblock_t, ins: ida_hexrays.minsn_t):  # type: ignore[override]
        # Cheap opcode pre-filter: if no Z3 rule targets this opcode, skip.
        try:
            if (
                self._allowed_root_opcodes
                and ins.opcode not in self._allowed_root_opcodes
            ):
                return None
        except Exception:
            pass
        return super().get_optimized_instruction(blk, ins)
