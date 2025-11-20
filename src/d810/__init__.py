"""D810 - IDA Pro deobfuscation plugin.

This module imports all optimizer handlers to ensure they are registered
with the registry before the plugin tries to access them.
"""

# Import all optimizer handlers to trigger registration
# This must happen before d810.manager or d810.hexrays.hexrays_hooks are imported
import d810.optimizers.microcode.instructions  # noqa: F401

__all__ = ["optimizers"]
