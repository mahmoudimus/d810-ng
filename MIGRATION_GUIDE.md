# Migration Guide: Refactored D810 Architecture

This guide explains the new refactored architecture and how to migrate existing rules to the new system.

## Overview of Changes

The d810 codebase has been refactored following the plan in `REFACTORING.md`. The key improvements are:

1. **Composition over Inheritance** - Clear interfaces using Protocols instead of deep inheritance
2. **Declarative DSL** - Rules written using operator overloading instead of manual AST construction
3. **Self-Verification** - Rules automatically prove their own correctness using Z3
4. **Better Testability** - Single generic test verifies all rules

## New Core Components

### 1. OptimizationContext (`d810/optimizers/core.py`)

Replaces scattered instance variables with an immutable context object:

```python
@dataclass(frozen=True)
class OptimizationContext:
    mba: mba_t
    maturity: int
    config: Dict[str, Any]
    logger: logging.Logger
    log_dir: str
```

**Benefits:**
- No more `self.mba`, `self.cur_maturity`, etc. scattered everywhere
- Rules become stateless and easily testable
- All dependencies are explicit

### 2. Symbolic Expression DSL (`d810/optimizers/dsl.py`)

Allows writing rules in natural mathematical syntax:

```python
from d810.optimizers.dsl import Var, Const, ONE

x = Var("x")
y = Var("y")

# Instead of: AstNode(m_xor, AstLeaf("x"), AstLeaf("y"))
pattern = x ^ y

# Instead of: AstNode(m_add, AstNode(m_bnot, AstLeaf("x")), AstConstant("1", 1))
pattern = ~x + ONE
```

**Supported Operators:**
- `+` → m_add
- `-` → m_sub
- `^` → m_xor
- `&` → m_and
- `|` → m_or
- `*` → m_mul
- `<<` → m_shl
- `>>` → m_shr
- `~` → m_bnot
- `-x` → m_neg (unary)

### 3. VerifiableRule Base Class (`d810/optimizers/rules.py`)

Self-verifying rule base class with automatic Z3 verification:

```python
class XorFromOrAndSub(VerifiableRule):
    name = "XorFromOrAndSub"
    description = "(x | y) - (x & y) => x ^ y"

    @property
    def pattern(self):
        return (x | y) - (x & y)

    @property
    def replacement(self):
        return x ^ y
```

**Automatic Features:**
- Z3 verification of correctness
- Auto-registration for testing
- Rich error messages with counterexamples

## Migrating Existing Rules

### Before (Old Style)

```python
from d810.expr.ast import AstConstant, AstLeaf, AstNode
from d810.optimizers.microcode.instructions.pattern_matching.handler import PatternMatchingRule
from ida_hexrays import *

class Xor_HackersDelightRule_1(PatternMatchingRule):
    @property
    def PATTERN(self) -> AstNode:
        return AstNode(
            m_sub,
            AstNode(m_or, AstLeaf("x_0"), AstLeaf("x_1")),
            AstNode(m_and, AstLeaf("x_0"), AstLeaf("x_1")),
        )

    @property
    def REPLACEMENT_PATTERN(self) -> AstNode:
        return AstNode(m_xor, AstLeaf("x_0"), AstLeaf("x_1"))
```

### After (New Style)

```python
from d810.optimizers.dsl import Var
from d810.optimizers.rules import VerifiableRule

# Define variables once at module level
x = Var("x")
y = Var("y")

class XorFromOrAndSub(VerifiableRule):
    name = "XorFromOrAndSub"
    description = "(x | y) - (x & y) => x ^ y (Hacker's Delight identity)"

    @property
    def pattern(self):
        return (x | y) - (x & y)

    @property
    def replacement(self):
        return x ^ y
```

### Migration Steps

1. **Import the new base class and DSL:**
   ```python
   from d810.optimizers.dsl import Var, Const, ONE, TWO, ZERO
   from d810.optimizers.rules import VerifiableRule
   ```

2. **Define symbolic variables at module level:**
   ```python
   x = Var("x")
   y = Var("y")
   a = Var("a")
   b = Var("b")
   c1 = Const("c1")  # Matches any constant
   one = Const("one", 1)  # Matches only the value 1
   ```

3. **Inherit from VerifiableRule:**
   ```python
   class MyRule(VerifiableRule):
   ```

4. **Add name and description:**
   ```python
   name = "MyRuleName"
   description = "What this rule does and why"
   ```

5. **Convert PATTERN → pattern:**
   - Change from imperative AST construction to declarative expressions
   - Use Python operators instead of AstNode constructors

6. **Convert REPLACEMENT_PATTERN → replacement:**
   - Same process as pattern

7. **Add constraints if needed:**
   ```python
   def get_constraints(self, z3_vars):
       # Only if rule is conditional
       return [z3_vars["c2"] == ~z3_vars["c1"]]
   ```

## Testing Your Migrated Rules

### Automatic Verification

Once you've migrated a rule, it's automatically verified:

```python
# tests/unit/optimizers/test_verifiable_rules.py

# Just import your module
import d810.optimizers.microcode.instructions.pattern_matching.rewrite_xor_refactored

# That's it! The test automatically finds and verifies your rules
```

Run the test:
```bash
pytest tests/unit/optimizers/test_verifiable_rules.py -v
```

### What Verification Checks

The Z3 verification proves that:
- `pattern` and `replacement` are semantically equivalent for **all** possible inputs
- The transformation preserves program behavior
- There are no edge cases where the rule breaks

### If Verification Fails

You'll get a detailed error message:

```
--- VERIFICATION FAILED ---
Rule:        MyBuggyRule
Description: My rule description
Identity:    (x + y) => (x - y)
Counterexample: {'x': 5, 'y': 3}

When x=5, y=3:
  pattern gives: 8
  replacement gives: 2

This rule does NOT preserve semantics and should not be used.
```

## Advanced Features

### Rules with Constraints

Some rules are only valid under certain conditions:

```python
class ConditionalRule(VerifiableRule):
    name = "ConditionalRule"
    description = "(x & c1) | (x & c2) => x when c2 == ~c1"

    @property
    def pattern(self):
        return (x & c1) | (x & c2)

    @property
    def replacement(self):
        return x

    def get_constraints(self, z3_vars):
        # This rule only works when c2 is the bitwise NOT of c1
        return [z3_vars["c2"] == ~z3_vars["c1"]]
```

### Bidirectional Rules

Sometimes you want both directions of a transformation:

```python
class NegExpand(VerifiableRule):
    """Expand -x into two's complement form"""
    name = "NegExpand"
    description = "-x => ~x + 1"

    @property
    def pattern(self):
        return -x

    @property
    def replacement(self):
        return ~x + ONE

class NegSimplify(VerifiableRule):
    """Simplify two's complement into negation"""
    name = "NegSimplify"
    description = "~x + 1 => -x"

    @property
    def pattern(self):
        return ~x + ONE

    @property
    def replacement(self):
        return -x
```

Both pass verification because they're mathematically equivalent.

## Benefits of the New System

### For Rule Authors

- **Faster development**: Write rules in natural notation
- **Fewer bugs**: Z3 catches errors before they reach production
- **Self-documenting**: Code reads like the math it represents
- **No manual tests**: Verification is automatic

### For Maintainers

- **Easier review**: Rules are concise and readable
- **Confidence**: Every rule is mathematically proven correct
- **Less test code**: One generic test for all rules
- **Better errors**: Z3 provides concrete counterexamples

### For Users

- **More reliable**: Bugs caught before release
- **Faster fixes**: Easy to verify fixes are correct
- **Better documentation**: Rules explain what they do

## Gradual Migration Strategy

You don't have to migrate everything at once:

1. **Phase 1**: New rules use the new system (already done)
2. **Phase 2**: Migrate high-risk rules first (complex transformations)
3. **Phase 3**: Migrate frequently-used rules
4. **Phase 4**: Migrate remaining rules as time permits

Both old and new styles can coexist during migration.

## Getting Help

- See `REFACTORING.md` for the full design rationale
- See `src/d810/optimizers/microcode/instructions/pattern_matching/rewrite_xor_refactored.py` for examples
- See `src/d810/optimizers/microcode/instructions/pattern_matching/rewrite_neg_refactored.py` for more examples
- See `tests/unit/optimizers/test_verifiable_rules.py` for the test setup

## Phase 2: Flow Optimization Services (NEW!)

### Composable Services (`d810/optimizers/microcode/flow/flattening/services.py`)

Flow optimizations have been decomposed into single-responsibility services:

```python
@dataclass(frozen=True)
class Dispatcher:
    """Immutable representation of a control-flow dispatcher."""
    entry_block: mblock_t
    state_variable: mop_t
    comparison_values: List[int]
    # ...

class DispatcherFinder(Protocol):
    """Protocol for finding dispatchers."""
    def find(self, context: OptimizationContext) -> List[Dispatcher]:
        ...

class PathEmulator:
    """Emulates paths to resolve state variables."""
    def resolve_target(
        self, context, from_block, dispatcher
    ) -> mblock_t | None:
        ...

class CFGPatcher:
    """Applies changes to the control flow graph."""
    @staticmethod
    def redirect_edge(context, from_block, to_block) -> int:
        ...
```

### Refactored Unflattener (`unflattener_refactored.py`)

**Before (700+ lines):**
```python
class GenericDispatcherUnflatteningRule(GenericUnflatteningRule):
    # God object that does EVERYTHING:
    # - Finding dispatchers
    # - Emulating paths
    # - Patching CFG
    # - Managing state
    # 700+ lines of tightly coupled code
```

**After (~100 lines):**
```python
class UnflattenerRule:
    """Clean coordinator using composition."""

    def __init__(self, finder, emulator, patcher):
        self._finder = finder      # Dependency injection
        self._emulator = emulator  # Easy to mock
        self._patcher = patcher    # Easy to test

    def apply(self, context, blk):
        dispatchers = self._finder.find(context)

        for dispatcher in dispatchers:
            for pred in dispatcher.entry_block.predset:
                target = self._emulator.resolve_target(...)
                self._patcher.redirect_edge(...)
```

**Testing Benefits:**
```python
# OLD: Need IDA environment, slow, brittle
def test_unflattening():
    ida.open_database("obfuscated.idb")  # Requires IDA!
    mba = get_mba(0x401000)              # Slow!
    rule = GenericDispatcherUnflatteningRule()
    changes = rule.optimize(mba.get_mblock(0))
    assert changes > 0  # Vague assertion

# NEW: Pure Python, fast, clear
def test_unflatten_single_dispatcher():
    mock_finder = Mock(spec=DispatcherFinder)
    mock_finder.find.return_value = [mock_dispatcher]

    rule = UnflattenerRule(mock_finder, mock_emulator, mock_patcher)
    changes = rule.apply(context, entry_block)

    assert changes == 1
    mock_emulator.resolve_target.assert_called_once()
```

## Next Steps

Remaining refactoring tasks from `REFACTORING.md`:

- [x] **Phase 1**: Declarative DSL with self-verifying rules ✅
- [x] **Phase 2**: Decompose flow optimizations into composable services ✅
- [ ] **Phase 3**: Create OptimizerManager to centralize the optimization loop
- [ ] **Phase 4**: Migrate all pattern matching rules to use the DSL
- [ ] **Phase 5**: Complete migration of flow optimization services

These will be tackled in future pull requests to keep changes manageable.
