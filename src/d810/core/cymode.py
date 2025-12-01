import dataclasses
import os

from .registry import survives_reload
from .singleton import SingletonMeta


def _get_default_cython_enabled() -> bool:
    """Check D810_NO_CYTHON env var to determine default state."""
    env_val = os.environ.get("D810_NO_CYTHON", "").lower()
    if env_val in ("1", "true", "yes"):
        return False
    return True


@survives_reload()
@dataclasses.dataclass(slots=True)
class CythonMode(metaclass=SingletonMeta):
    """
    Provides a controller to enable or disable the Cython-accelerated
    implementations of AST functions at runtime.

    Set D810_NO_CYTHON=1 environment variable to disable Cython at startup.
    """

    _enabled: bool = dataclasses.field(default_factory=_get_default_cython_enabled)

    def _set_flag(self, value: bool) -> None:
        self._enabled = bool(value)

    def enable(self) -> None:
        """Point the public API to the fast Cython implementations."""
        if not self._enabled:
            self._set_flag(True)
            print("Cython AST implementation ENABLED.")

    def disable(self) -> None:
        """Point the public API to the pure Python implementations for debugging."""
        if self._enabled:
            self._set_flag(False)
            print("Cython AST implementation DISABLED (using pure Python).")

    def is_enabled(self) -> bool:
        """Check if the Cython implementation is currently active."""
        return self._enabled

    def toggle(self) -> None:
        """Toggle the Cython implementation on/off."""
        if self._enabled:
            self.disable()
        else:
            self.enable()
