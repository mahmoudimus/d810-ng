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
        # Track if any rule has no PATTERN (pattern-less rules match any opcode)
        self._has_patternless_rule: bool = False

    def add_rule(self, rule: Z3Rule) -> bool:  # type: ignore[override]
        ok = super().add_rule(rule)
        if not ok:
            return False
        try:
            pat = rule.PATTERN
            if pat is None:
                # Rule has no PATTERN - it uses custom check_and_replace logic
                # and can match any opcode, so disable the pre-filter entirely
                # by clearing _allowed_root_opcodes (also checked by base class)
                self._has_patternless_rule = True
                self._allowed_root_opcodes.clear()
            elif isinstance(pat, AstNode) and pat.opcode is not None:
                # Only add to filter if we haven't disabled it
                if not self._has_patternless_rule:
                    self._allowed_root_opcodes.add(int(pat.opcode))
        except Exception:
            pass
        return True

    def get_optimized_instruction(self, blk: ida_hexrays.mblock_t, ins: ida_hexrays.minsn_t):  # type: ignore[override]
        # The opcode pre-filter is now handled by clearing _allowed_root_opcodes
        # when a patternless rule is added, which also disables the base class filter.
        return super().get_optimized_instruction(blk, ins)
