import dataclasses

from .registry import survives_reload
from .singleton import SingletonMeta


@survives_reload()
@dataclasses.dataclass(slots=True)
class CythonMode(metaclass=SingletonMeta):
    """
    Provides a controller to enable or disable the Cython-accelerated
    implementations of AST functions at runtime.
    """

    _enabled: bool = dataclasses.field(default=True)

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
