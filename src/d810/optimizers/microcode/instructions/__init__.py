"""Instruction-level optimizer handlers."""

# Import all optimizer submodules to trigger registration
from . import analysis  # noqa: F401
from . import chain  # noqa: F401
from . import early  # noqa: F401
from . import pattern_matching  # noqa: F401
from . import peephole  # noqa: F401
from . import z3  # noqa: F401
