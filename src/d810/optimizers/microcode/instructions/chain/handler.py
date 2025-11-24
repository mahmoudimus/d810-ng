import abc

from d810.optimizers.microcode.instructions.handler import (
    InstructionOptimizationRule,
    InstructionOptimizer,
)


class ChainSimplificationRule(InstructionOptimizationRule):

    @abc.abstractmethod
    def check_and_replace(self, blk, ins):
        """Return a replacement instruction if the rule matches, otherwise None."""


class ChainOptimizer(InstructionOptimizer):
    RULE_CLASSES = [ChainSimplificationRule]

    def __init__(self, maturities, stats, log_dir=None):
        super().__init__(maturities, stats, log_dir)
        # Only consider binary associative ops chains
        from ida_hexrays import m_add, m_and, m_or, m_sub, m_xor

        self._allowed_root_opcodes = {m_xor, m_and, m_or, m_add, m_sub}
