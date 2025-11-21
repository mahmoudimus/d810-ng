"""Instruction-level optimizer handlers.

This module imports all optimizer submodules to ensure they register
with the InstructionOptimizer registry.
"""

# Import handler classes to trigger registration
from d810.optimizers.microcode.instructions.handler import (
    InstructionOptimizationRule,
    InstructionOptimizer,
)

# Import all optimizer modules to register them
from d810.optimizers.microcode.instructions.analysis import handler as analysis_handler
from d810.optimizers.microcode.instructions.chain import handler as chain_handler
from d810.optimizers.microcode.instructions.early import handler as early_handler
from d810.optimizers.microcode.instructions.pattern_matching import handler as pattern_handler
from d810.optimizers.microcode.instructions.peephole import handler as peephole_handler
from d810.optimizers.microcode.instructions.z3 import handler as z3_handler

__all__ = [
    "InstructionOptimizationRule",
    "InstructionOptimizer",
]
