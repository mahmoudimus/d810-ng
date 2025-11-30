"""Pattern matching optimizer handlers.

Rules in this module are automatically discovered and registered by the
reloadable scanner. Both old (ast-based) and refactored (DSL-based) rules
are registered automatically when their modules are imported.
"""

# Import handler base classes for type checking
try:
    from .handler import PatternMatchingRule, GenericPatternRule
    __all__ = ["PatternMatchingRule", "GenericPatternRule"]
except ImportError:
    # Allow module to be imported without IDA for unit testing
    # Rule modules can still be imported individually
    __all__ = []
