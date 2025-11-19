"""D810 - IDA Pro deobfuscation plugin.

This module uses the discovery mechanism to scan and import all submodules,
ensuring all optimizer handlers are registered before the plugin tries to
access them.
"""

import pathlib
import sys

# Discover and import all modules in the package during initial load
# This ensures optimizer classes are registered before the plugin manager
# tries to look them up from the registry
_package_root = pathlib.Path(__file__).parent
if _package_root.exists():
    from d810.reloadable import _Scanner

    _Scanner.scan(
        package_path=[str(_package_root)],
        prefix="d810.",
        callback=None,
        skip_packages=False,
    )

__all__ = ["optimizers"]
