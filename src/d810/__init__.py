"""D810 - IDA Pro deobfuscation plugin.

Module discovery happens automatically:
- During initial import (for tests and direct usage)
- During plugin reload (for hot-reloading in IDA)
"""

import pathlib
from d810.reloadable import _Scanner

# Discover and load all modules in the package
# This ensures optimizer classes are registered when d810 is imported
_package_root = pathlib.Path(__file__).parent
_Scanner.scan(
    package_path=[str(_package_root)],
    prefix="d810.",
    callback=None,
    skip_packages=False,
)

__all__ = []
