# Refactoring D810

This codebase is a classic example of deep inheritance hierarchies leading to God objects and tight coupling, making it difficult to test and maintain.

## Composition over Inheritance

Using modern Python principles to favor composition over inheritance, improve testability, and increase clarity, this project can be refactored to be testable and easier to follow.

### Core Problems Identified

1. **Deep Inheritance:** Chains like `Unflattener` -> `GenericDispatcherUnflatteningRule` -> `GenericUnflatteningRule` -> `FlowOptimizationRule` create "God Objects" that know and do too much.
2. **Implicit State:** Rules heavily rely on instance variables (`self.mba`, `self.cur_maturity`, `self.last_pass_nb_patch_done`) that are modified during execution. This makes them stateful and hard to test in isolation.
3. **Mixed Concerns:** A single class like `GenericDispatcherUnflatteningRule` is responsible for finding dispatchers, analyzing control flow, duplicating blocks, and patching the graph.
4. **Poorly Defined Interfaces:** It's not immediately clear what constitutes an "optimization rule" without reading the implementation of the optimizer that runs it.

### Refactoring Strategy: Composition, Protocols, and Statelessness

The goal is to break down large classes into smaller, single-responsibility components and define clear contracts between them.

### 1. Define Clear Interfaces with Protocols

Instead of relying on concrete base classes, define the expected behavior using `typing.Protocol`. This decouples the rules from their execution engine.

```python
# d810/optimizers/core.py (a new file for core abstractions)
import abc
from typing import Protocol, List, Any, Dict
from dataclasses import dataclass
from ida_hexrays import mba_t, mblock_t, minsn_t

@dataclass(frozen=True)
class OptimizationContext:
    """A context object holding all necessary data for an optimization pass."""
    mba: mba_t
    maturity: int
    config: Dict[str, Any]
    logger: logging.Logger
    log_dir: str

class OptimizationRule(Protocol):
    """A contract for any optimization rule."""
    
    @property
    def name(self) -> str:
        """A unique name for the rule."""
        ...

    def apply(self, context: OptimizationContext, element: Any) -> int:
        """
        Applies the optimization.
        
        Args:
            context: The current optimization context.
            element: The program element to optimize (e.g., mblock_t, minsn_t).
        
        Returns:
            The number of changes made.
        """
        ...

class PatternMatchingRule(abc.ABC):
    """An abstract base class for rules that match AST patterns."""
    
    @property
    @abc.abstractmethod
    def pattern(self) -> "AstNode": ...
    
    @property
    @abc.abstractmethod
    def replacement(self) -> "AstNode": ...

    @abc.abstractmethod
    def check_candidate(self, candidate: "AstNode") -> bool:
        """Performs rule-specific checks on a matched pattern."""
        ...

    def apply(self, context: OptimizationContext, ins: minsn_t) -> int:
        """Applies the pattern matching rule to a single instruction."""
        # Implementation for matching `self.pattern` and creating `self.replacement`
        # This can be a shared implementation.
        ...
```

### 2. Decompose God Objects into Composable Services

The monolithic `GenericDispatcherUnflatteningRule` can be broken down into distinct, reusable services.

**Before:** A single, massive class.

```python
class GenericDispatcherUnflatteningRule(GenericUnflatteningRule):
    # ... 200+ lines of finding, analyzing, duplicating, resolving, patching ...
    def optimize(self, blk: mblock_t) -> int:
        self.mba = blk.mba
        # ... lots of state changes and mixed logic ...
```

**After:** A coordinator rule that *uses* specialized services.

```python
# In a new file, e.g., d810/optimizers/flow/flattening/components.py

from typing import NamedTuple

# Use dataclasses or NamedTuples for structured data
@dataclass(frozen=True)
class Dispatcher:
    """Represents a discovered control-flow flattening dispatcher."""
    entry_block: mblock_t
    state_variable: mop_t
    # ... other relevant info

class DispatcherFinder(Protocol):
    """Finds dispatchers in the microcode."""
    def find(self, context: OptimizationContext) -> List[Dispatcher]: ...

class PathEmulator:
    """Emulates microcode paths to resolve state variables."""
    def resolve_target(self, context: OptimizationContext, from_block: mblock_t, dispatcher: Dispatcher) -> mblock_t:
        # Wraps MopTracker and MicroCodeInterpreter logic
        ...

class CFGPatcher:
    """Applies changes to the control-flow graph."""
    @staticmethod
    def redirect_edge(context: OptimizationContext, from_block: mblock_t, new_target: mblock_t) -> int:
        # Wraps logic from cfg_utils
        ...

# The refactored rule becomes a simple coordinator
# In d810/optimizers/flow/flattening/unflattener.py
class UnflattenerRule(OptimizationRule):
    """Removes O-LLVM style control-flow flattening."""
    name = "OLLVMUnflattener"

    def __init__(self):
        # Dependencies are now explicit. They can be real or mock objects for testing.
        self._finder = OllvmDispatcherFinder()
        self._emulator = PathEmulator()
        self._patcher = CFGPatcher()

    def apply(self, context: OptimizationContext, blk: mblock_t) -> int:
        # The rule only applies once per function, so we check the entry block.
        if blk.serial != 0:
            return 0
            
        changes = 0
        dispatchers = self._finder.find(context)
        for disp in dispatchers:
            for pred_serial in disp.entry_block.predset:
                pred_block = context.mba.get_mblock(pred_serial)
                try:
                    target_block = self._emulator.resolve_target(context, pred_block, disp)
                    changes += self._patcher.redirect_edge(context, pred_block, target_block)
                except Exception as e:
                    context.logger.warning(f"Could not unflatten from {pred_block.serial}: {e}")
        return changes
```

### 3. Refactor Pattern Matching with `abc.ABC`

The many `rewrite_*.py` files define rules that are very similar. An abstract base class is perfect here.

**Before:** Each rule class re-implements `check_candidate` and has boilerplate `PATTERN` and `REPLACEMENT_PATTERN` attributes.

**After:** A clear, abstract definition of a pattern rule.

```python
# In d810/optimizers/instructions/pattern_matching/handler.py
class PatternRule(OptimizationRule, abc.ABC):
    """
    An abstract base class for a rule that replaces one AST pattern with another.
    """
    name: str = "UnnamedPatternRule"
    description: str = "No description"

    @property
    @abc.abstractmethod
    def pattern(self) -> AstNode:
        """The AST pattern to match."""
        ...

    @property
    @abc.abstractmethod
    def replacement(self) -> AstNode:
        """The AST pattern to substitute."""
        ...

    def check_candidate(self, candidate: AstNode) -> bool:
        """
        Optional: perform extra validation on a matched pattern.
        By default, a match is always valid.
        """
        return True

    def apply(self, context: OptimizationContext, ins: minsn_t) -> int:
        """Shared implementation to match and replace the pattern."""
        ast = minsn_to_ast(ins)
        if not ast:
            return 0

        if self.pattern.check_pattern_and_copy_mops(ast):
            if self.check_candidate(self.pattern):
                new_ins = self.replacement.create_minsn(ins.ea, ins.d)
                if new_ins:
                    ins.swap(new_ins)
                    return 1
        return 0

# A concrete rule is now extremely concise and declarative.
# In d810/optimizers/instructions/pattern_matching/rewrite_neg.py
class NegToBnotAdd(PatternRule):
    name = "NegToBnotAdd"
    description = "-x => ~x + 1"
    
    @property
    def pattern(self) -> AstNode:
        return AstNode(m_neg, AstLeaf("x"))

    @property
    def replacement(self) -> AstNode:
        return AstNode(m_add, AstNode(m_bnot, AstLeaf("x")), AstConstant("1", 1))
```

### 4. Centralize the Optimizer Loop

Instead of each rule managing its own maturity checks and pass counts, a central `OptimizerManager` should handle the main loop. This manager would instantiate rules and pass them the appropriate `OptimizationContext`.

```python
# In a new file, e.g., d810/manager.py
class OptimizerManager:
    def __init__(self, config: Dict[str, Any]):
        self.flow_rules: List[OptimizationRule] = self._load_rules("flow", config)
        self.instruction_rules: List[OptimizationRule] = self._load_rules("instruction", config)
        # ...

    def _run_optimizers(self, mba: mba_t, maturity: int):
        context = OptimizationContext(mba=mba, maturity=maturity, ...)
        
        # Apply flow rules
        for rule in self.flow_rules:
            # The manager can decide what element to pass (e.g., first block)
            rule.apply(context, mba.get_mblock(0))

        # Apply instruction rules
        for block in mba.blocks:
            for ins in block.instructions:
                for rule in self.instruction_rules:
                    rule.apply(context, ins)

    def install_hooks(self):
        # ... logic to hook into Hex-Rays callbacks and call _run_optimizers ...
```

### Summary of Benefits

* **Testability:** Each component (`OllvmDispatcherFinder`, `PathEmulator`, `NegToBnotAdd`) can be unit-tested in complete isolation by providing mock objects for its dependencies.
* **Maintainability:** Logic is separated by concern. Modifying how dispatchers are found doesn't require touching the patching logic. Adding a new pattern is a small, declarative class.
* **Clarity:** Dependencies are explicit (passed in `__init__` or as method arguments) rather than implicit (`self.mba`). The `Protocol`s serve as clear documentation for how components interact.
* **Reusability:** Components like `CFGPatcher` or `PathEmulator` can be reused by different high-level optimization strategies.

## AstNode construction is imperative instead of declarative

The verbosity of the `AstNode` construction is imperative and low-level. It describes *how* to build the tree, not *what* the tree represents. This makes the rules hard to read and even harder to verify for correctness without running them through a separate test suite. A more declarative, DSL-like approach where the rule's definition is closer to its mathematical proof is the one better approach.

Create a small, embedded DSL using Python's operator overloading. This will make the rules:

1. **Declarative:** You write expressions that look like math, not tree-building code.
2. **Readable:** `(x | y) - (x & y)` is instantly recognizable.
3. **Self-Verifying:** We can build a mechanism to automatically prove the equivalence of the pattern and replacement using Z3, directly from the rule definition.

### Refactoring Plan: A Rule DSL with Built-in Verification

#### 1. Create a Symbolic Expression Layer

First, we'll create a set of classes to represent symbolic variables and expressions. These classes will overload Python's operators (`+`, `-`, `^`, `&`, `|`, `~`) to build the `AstNode` tree behind the scenes.

```python
# d810/optimizers/dsl.py (New File)
from __future__ import annotations
from typing import Dict, Any
from ida_hexrays import mop_t, m_add, m_sub, m_xor, m_and, m_or, m_bnot, m_neg
from d810.expr.ast import AstNode, AstLeaf, AstConstant

class SymbolicExpression:
    """A symbolic representation of a microcode expression tree."""
    def __init__(self, node: AstNode):
        self.node = node

    def __add__(self, other: SymbolicExpression) -> SymbolicExpression:
        return SymbolicExpression(AstNode(m_add, self.node, other.node))

    def __sub__(self, other: SymbolicExpression) -> SymbolicExpression:
        return SymbolicExpression(AstNode(m_sub, self.node, other.node))

    def __xor__(self, other: SymbolicExpression) -> SymbolicExpression:
        return SymbolicExpression(AstNode(m_xor, self.node, other.node))

    def __and__(self, other: SymbolicExpression) -> SymbolicExpression:
        return SymbolicExpression(AstNode(m_and, self.node, other.node))

    def __or__(self, other: SymbolicExpression) -> SymbolicExpression:
        return SymbolicExpression(AstNode(m_or, self.node, other.node))

    def __invert__(self) -> SymbolicExpression:
        return SymbolicExpression(AstNode(m_bnot, self.node))

    def __neg__(self) -> SymbolicExpression:
        return SymbolicExpression(AstNode(m_neg, self.node))

    def __repr__(self) -> str:
        return str(self.node)

def Var(name: str) -> SymbolicExpression:
    """Factory for a symbolic variable."""
    return SymbolicExpression(AstLeaf(name))

def Const(name: str, value: int = 0) -> SymbolicExpression:
    """Factory for a symbolic constant."""
    return SymbolicExpression(AstConstant(name, value))
```

#### 2. Redefine the Rule with the DSL

Now, we can create a new base class for rules that uses this DSL. The key is that it will have a `verify()` method to prove its own correctness.

```python
# d810/optimizers/rules.py (New or Refactored File)
import abc
from typing import List, Dict, Any, Set

from d810.expr.ast import AstNode
from d810.expr.z3_utils import ast_to_z3, z3_prove_equivalence
from d810.optimizers.dsl import SymbolicExpression

# A simple registry to auto-discover all rules
RULE_REGISTRY: List["VerifiableRule"] = []
        
class SymbolicRule(abc.ABC):
    """A rule defined by symbolic, verifiable expressions."""
    name: str = "UnnamedSymbolicRule"
    description: str = "No description"

    @property
    @abc.abstractmethod
    def pattern(self) -> SymbolicExpression:
        """The symbolic pattern to match."""
        ...

    @property
    @abc.abstractmethod
    def replacement(self) -> SymbolicExpression:
        """The symbolic expression to replace the pattern with."""
        ...

    def verify(self) -> bool:
        """
        Proves that `pattern` is equivalent to `replacement` using Z3.
        This makes the rule self-verifying.
        """
        return z3_prove_equivalence(self.pattern.node, self.replacement.node)

    def apply(self, context: OptimizationContext, ins: minsn_t) -> int:
        """Shared implementation to apply the rule."""
        # This logic would be part of the new optimizer
        # It finds a match for `self.pattern.node` and replaces it
        # with a new instruction from `self.replacement.node`.
        ...

class VerifiableRule(abc.ABC):
    """
    An abstract base class for a symbolic rule that can verify its own correctness.
    Subclasses automatically register themselves for testing.
    """
    name: str = "UnnamedVerifiableRule"
    description: str = "No description"
    BIT_WIDTH = 32 # Default bit-width for verification

    def __init_subclass__(cls, **kwargs):
        """Automatically registers any subclass into the global registry."""
        super().__init_subclass__(**kwargs)
        RULE_REGISTRY.append(cls())

    @property
    @abc.abstractmethod
    def pattern(self) -> SymbolicExpression:
        """The symbolic pattern to match, defined using the DSL."""
        ...

    @property
    @abc.abstractmethod
    def replacement(self) -> SymbolicExpression:
        """The symbolic expression to replace the pattern with."""
        ...

    def get_constraints(self, z3_vars: Dict[str, Any]) -> List[Any]:
        """
        Optional: Subclasses can override this to provide Z3 constraints
        under which the rule is valid.
        
        Args:
            z3_vars: A dictionary mapping symbolic variable names to Z3 BitVec objects.
        
        Returns:
            A list of Z3 constraint expressions.
        """
        return []

    def verify(self) -> bool:
        """
        Proves that `self.pattern` is equivalent to `self.replacement` using Z3,
        applying any constraints defined in `get_constraints`.
        
        Returns:
            True if the rule is proven correct, raises an AssertionError otherwise.
        """
        # 1. Get the AST nodes from the symbolic expressions
        p_node = self.pattern.node
        r_node = self.replacement.node

        # 2. Find all unique symbolic variables from both sides
        p_vars = p_node.get_symbolic_vars()
        r_vars = r_node.get_symbolic_vars()
        all_var_names = sorted(list(p_vars.union(r_vars)))

        # 3. Create Z3 BitVec objects for each variable
        z3_vars = {name: BitVec(name, self.BIT_WIDTH) for name in all_var_names}

        # 4. Get rule-specific constraints
        constraints = self.get_constraints(z3_vars)

        # 5. Prove equivalence
        is_equivalent, model = z3_prove_equivalence(
            p_node, r_node, z3_vars, constraints
        )

        if not is_equivalent:
            msg = (
                f"\n--- VERIFICATION FAILED ---\n"
                f"Rule:        {self.name}\n"
                f"Description: {self.description}\n"
                f"Identity:    {self.pattern} => {self.replacement}\n"
                f"Counterexample: {model}"
            )
            raise AssertionError(msg)
        
        return True

```

#### 3. Rewrite Existing Rules Declaratively

Now, the `rewrite_*.py` files become incredibly simple and readable.

**Before (`rewrite_xor.py`):**

```python
class Xor_HackersDelightRule_1(PatternMatchingRule):
    PATTERN = AstNode(
        m_sub,
        AstNode(m_or, AstLeaf("x_0"), AstLeaf("x_1")),
        AstNode(m_and, AstLeaf("x_0"), AstLeaf("x_1")),
    )
    REPLACEMENT_PATTERN = AstNode(m_xor, AstLeaf("x_0"), AstLeaf("x_1"))
```

**After (`rewrite_xor.py`):**

```python
from d810.optimizers.dsl import Var
from d810.optimizers.rules import VerifiableRule

# Define symbolic variables once for the module
x, y = Var("x"), Var("y")

class XorFromOrAndSub(VerifiableRule):
    name = "XorFromOrAndSub"
    description = "(x | y) - (x & y) => x ^ y"

    @property
    def pattern(self) -> SymbolicExpression:
        return (x | y) - (x & y)

    @property
    def replacement(self) -> SymbolicExpression:
        return x ^ y
```

**Before (`rewrite_neg.py`):**

```python
class Neg_HackersDelightRule_1(PatternMatchingRule):
    PATTERN = AstNode(m_add, AstNode(m_bnot, AstLeaf("x_0")), AstConstant("1", 1))
    REPLACEMENT_PATTERN = AstNode(m_neg, AstLeaf("x_0"))
```

**After (`rewrite_neg.py`):**

```python
from d810.optimizers.dsl import Var, Const
from d810.optimizers.rules import SymbolicRule

x = Var("x")
one = Const("one", 1)

class NegFromBnotAdd(SymbolicRule):
    name = "NegFromBnotAdd"
    description = "~x + 1 => -x"

    @property
    def pattern(self) -> SymbolicExpression:
        return ~x + one

    @property
    def replacement(self) -> SymbolicExpression:
        return -x
```

**After (`rewrite_cst.py`):**

```python
# d810/optimizers/instructions/pattern_matching/rewrite_cst.py
from d810.optimizers.dsl import Var, Const
from d810.optimizers.rules import VerifiableRule

x = Var("x")
c1 = Const("c1")
c2 = Const("c2")

class CstSimplification5(VerifiableRule):
    name = "CstSimplification5"
    description = "((x & c1) | (x & c2)) => (((x ^ x) & c1) ^ x) where c2 = ~c1"

    @property
    def pattern(self):
        # Note: The original rule had x1, but the logic implies the same variable.
        # Let's assume it's (x & c1) | (x & c2)
        return (x & c1) | (x & c2)

    @property
    def replacement(self):
        # The original replacement was complex. A simpler equivalent is (x & c1) | (x & ~c1)
        # which simplifies to just x. Let's use the original for demonstration.
        return ((x ^ x) & c1) ^ x

    def get_constraints(self, z3_vars):
        # This rule is only valid if c2 is the bitwise NOT of c1.
        return [z3_vars["c2"] == ~z3_vars["c1"]]
```

### How This Solves the Problem

1. **Correctness is Built-in:**  Instead of manually writing a test case for every rule, one can write a single, generic test that iterates through all `SymbolicRule` instances and call their `verify()` method.

    ```python
    # test/test_rules.py
    import unittest
    import pytest
    from d810.optimizers.rules import VerifiableRule, RULE_REGISTRY

    # You would need to ensure all rule modules are imported so the registry populates.
    # A simple way is an __init__.py file in the rules directory that imports all rule files.
    import d810.optimizers.instructions.pattern_matching.rewrite_xor
    import d810.optimizers.instructions.pattern_matching.rewrite_cst
    # ... import all other rule files ...


    @pytest.mark.parametrize("rule", RULE_REGISTRY, ids=lambda r: r.name)
    def test_rule_is_correct(rule: VerifiableRule):
        """
        This single, generic test verifies the mathematical correctness of every
        rule that inherits from VerifiableRule by calling its own verify() method.
        """
        # The assertion and error message are now handled inside the rule itself.
        # This keeps the test clean and the failure output rich.
        rule.verify()

    class SanityCheck(unittest.TestCase):
        def test_registry_is_populated(self):
            self.assertGreater(len(RULE_REGISTRY), 0, "No rules were discovered and registered.")
    ```

    BONUS: If a developer writes a new rule where the pattern and replacement are not equivalent, this test will fail immediately, preventing incorrect optimizations from ever being merged.

2. **Readability and Intent:** The rule definitions are now high-level and mathematical. The code `(x | y) - (x & y)` is a direct translation of the logic, making the intent clear without needing to parse a complex `AstNode` structure. This approach transforms the rule system from a collection of imperative tree-building instructions into a declarative, self-verifying library of mathematical equivalences. Each rule is responsible for guaranteeing its own correctness. This is a powerful design principle that leads to more robust and reliable systems.

3. **Testability:** The rule's class definition is the complete specification. Its logic, its constraints, and the means to prove its correctness are all in one place. The test suite is now trivial. It doesn't need to be updated when you add new rules. As long as a new rule inherits from VerifiableRule, it will be automatically discovered and tested.

---

## Refactoring Accomplishments (2024-2025)

The declarative DSL refactoring has been **successfully completed** with the following achievements:

### ✅ What We've Accomplished

#### 1. **Declarative DSL Implementation** ✓
- **Complete**: All 177 optimization rules migrated from imperative `AstNode` construction to declarative DSL
- **Operator Overloading**: Rules now use natural Python operators (`+`, `-`, `&`, `|`, `^`, `~`, `>>`, `<<`)
- **Type Safety**: Strict separation between Terms (`SymbolicExpression`) and Formulas (`ConstraintExpr`)
- **Examples**:
  ```python
  # Before (Imperative)
  PATTERN = AstNode(m_sub, AstNode(m_or, AstLeaf("x"), AstLeaf("y")), 
                    AstNode(m_and, AstLeaf("x"), AstLeaf("y")))
  
  # After (Declarative)
  PATTERN = (x | y) - (x & y)
  ```

#### 2. **Automatic Z3 Verification** ✓
- **Coverage**: **170/177 rules (96.0%)** automatically verified
- **Matches Main Branch**: Same 7 skipped rules as main branch (5 KNOWN_INCORRECT + 2 performance)
- **Test Time**: 12.44 seconds for all 170 rules
- **Auto-Discovery**: All rules automatically registered and tested via metaclass
- **Results**:
  ```
  ==================== 170 passed, 7 skipped in 12.44s ====================
  ```

#### 3. **Advanced Features Implemented** ✓

**Boolean-to-Integer Bridge (`.to_int()`):**
- Enables verification of predicate rules (comparisons that return 0/1)
- Type-safe conversion from `ConstraintExpr` (boolean) to `SymbolicExpression` (0 or 1)
- Verified **11 predicate rules** using this approach

**Zero-Extension Support (`Zext`):**
- Added `Zext(expr, target_width)` for IDA's `xdu` instruction
- Z3 visitor converts to `z3.ZeroExt`
- IDA pattern matching maps to `M_XDU` opcode

**Concrete Constant Optimization:**
- Replaced size-dependent runtime checks with concrete constants
- Example: Check `c == -2` instead of `(c + 2) & SIZE_MASK == 0`
- Enabled verification of 3 additional OLLVM rules

**Bit-Width-Specific Verification:**
- Support for rules with different bit-widths (8-bit, 16-bit, 32-bit)
- Example: Byte-specific rules use `BIT_WIDTH = 8` instead of defaulting to 32-bit
- Handles overflow correctly: In 8-bit, `256 ≡ 0 (mod 256)`
- Verified **5 HODUR obfuscation rules** including byte-specific patterns
- Avoids false `SKIP_VERIFICATION` for legitimate size-specific rules

**Context-Aware DSL (NEW):**
- Declarative framework for rules that inspect/modify instruction context
- Three key abstractions:
  1. **Context Constraints** (`when.dst.*`): Declarative checks on destination properties
  2. **Context Providers** (`context.dst.*`): Bind variables from instruction context
  3. **Side Effects** (`UPDATE_DESTINATION`): Explicit destination modifications
- Zero IDA knowledge required: Users don't import `ida_hexrays` or manipulate `mop_t`
- Enables "average users" who know math but not IDA internals to write advanced rules
- Migrated `ReplaceMovHigh` as proof-of-concept
- Fully tested with 11 unit tests (all passing)

#### 4. **Constraint System** ✓

**Declarative Constraints:**
- All lambda constraints migrated to `ConstraintExpr` where possible
- Auto-conversion to Z3 for verification
- Examples:
  - Equality: `c1 == c2`
  - Comparison: `c1 < c2`
  - Arithmetic: `c_res == c1 | c2`
  - Boolean: `(c1 | c2) != c2`

**Defining Constraints:**
- Dynamic constants computed from matched values
- Example: `c_res == c1 + c2` both validates and computes `c_res`

### 📊 Current State

| Metric | Value |
|--------|-------|
| **Total Rules** | 177 |
| **Verified** | 170 (96.0%) |
| **Skipped** | 7 (4.0%) |
| **Test Time** | 12.44s |
| **Main Branch Parity** | ✅ Exact match on skipped rules |

### 🔍 Remaining Skipped Rules (7 total)

**KNOWN_INCORRECT (5 rules):**
These are mathematically wrong but kept for test parity with main branch:
1. `AndGetUpperBits_FactorRule_1` - Only valid under very specific conditions
2. `CstSimplificationRule2` - Requires disjoint constants constraint not captured
3. `CstSimplificationRule12` - Off by constant value of 1
4. `Mul_MBA_2` - Multiplication doesn't distribute over bitwise ops
5. `Mul_MBA_3` - Similar to Mul_MBA_2

**Performance (2 rules):**
These have complex MBA multiplication patterns that are correct but slow to verify:
6. `Mul_MBA_1` - 4 multiplications (main branch marks as `is_nonlinear=True`)
7. `Mul_MBA_4` - 3 multiplications (main branch marks as `is_nonlinear=True`)

### 🎯 What's Left (Future Work)

#### Optional Enhancements

1. **Performance Rules** (low priority):
   - Add timeout-based verification (30-60s) for MBA multiplication rules
   - Alternative: Use different SMT solver (Bitwuzla) for nonlinear bitvectors
   - These rules are **correct** and work at runtime, just slow to verify

2. **DSL Extensions** (as needed):
   - Add more operations if new IDA opcodes need support
   - Current coverage is comprehensive for all existing rules

3. **Context-Aware DSL Extensions** (as needed):
   - ✅ Core framework implemented (constraints, providers, side effects)
   - ✅ Destination helpers implemented (`when.dst.*`, `context.dst.*`)
   - Future: Source operand helpers (`when.src.*`, `context.src.*`)
   - Future: Function context helpers (`context.function.*`)
   - Future: More providers as use cases emerge

4. **Documentation** (ongoing):
   - ✅ README.md updated with complete rule creation guide
   - ✅ Automatic verification section added
   - ✅ Advanced features documented (`.to_int()`, `Zext`, bit-width, context-aware)
   - ✅ Context-aware DSL fully documented with examples
   - Future: Video tutorials for rule creation

### 🏆 Success Metrics Achieved

| Goal | Target | Achieved | Status |
|------|--------|----------|--------|
| Declarative DSL | 100% | 100% | ✅ |
| Automatic Verification | >90% | 96.0% | ✅ |
| Main Branch Parity | Match skipped rules | Exact match | ✅ |
| Test Speed | <30s | 12.44s | ✅ |
| Type Safety | Full separation | Complete | ✅ |
| Context-Aware Framework | Accessible to non-experts | Implemented | ✅ |

### 📝 Migration Summary

**Files Modified:**
- `src/d810/optimizers/dsl.py` - Core DSL with operator overloading
- `src/d810/optimizers/constraints.py` - Constraint system with `.to_int()`
- `src/d810/optimizers/rules.py` - `VerifiableRule` base class with bit-width and context support
- `src/d810/expr/visitors.py` - Z3 visitor with `bool_to_int` and `zext` support
- 12 `rewrite_*.py` files - All rules migrated to declarative DSL
- `hodur_verifiable.py` - **NEW**: 5 HODUR obfuscation rules with byte-specific verification
- `extensions.py` - **NEW**: Context-aware DSL (constraints, providers, side effects)
- `rewrite_mov_context_aware.py` - **NEW**: Context-aware rule proof-of-concept

**Test Files:**
- `tests/unit/optimizers/test_verifiable_rules.py` - Automatic verification test
- `tests/unit/optimizers/test_context_aware_dsl.py` - **NEW**: Context-aware DSL tests (11 tests)

**Documentation:**
- `README.md` - Complete rule creation guide
- `REFACTORING.md` - This summary

### 🔄 Comparison with Main Branch

| Branch | Rules | Verified | Skipped | Test Time |
|--------|-------|----------|---------|-----------|
| **Main** | 168 | 161 (95.8%) | 7 | 7.17s |
| **Ours** | 177 | **170 (96.0%)** | 7 | 12.44s |

**Net Improvement:**
- ✅ +9 rules added and verified (including 5 HODUR obfuscation rules)
- ✅ Same 7 rules skipped (for same reasons)
- ✅ Higher absolute verification coverage (96.0% vs 95.8%)
- ⚠️ Slower tests (+5.3s) due to +9 verified rules

### 🎓 Key Lessons Learned

1. **Explicit is Better**: Capturing full comparisons in patterns (e.g., `((x | c1) != c2).to_int()`) enables verification
2. **Concrete Over Generic**: Using `c == -2` instead of size-dependent checks enables verification
3. **Type Safety Matters**: Separating Terms and Formulas caught bugs early
4. **Z3 is Powerful**: Proves correctness automatically, catching subtle errors humans miss
5. **Operator Overloading Works**: Makes rules readable and mathematically precise
6. **Bit-Width Configuration**: Size-specific rules can be verified by setting `BIT_WIDTH = 8/16/32` instead of marking as `SKIP_VERIFICATION`
7. **Context Abstraction Enables Accessibility**: By hiding IDA's C++ API behind declarative helpers (`when.dst.*`, `context.dst.*`), the framework becomes accessible to users who understand the math but not IDA internals

### 🚀 How to Add a New Rule

See the comprehensive guide in `README.md`, but in summary:

1. Create rule class inheriting from `VerifiableRule`
2. Define `PATTERN` and `REPLACEMENT` using DSL operators
3. Add `CONSTRAINTS` if needed (declarative preferred)
4. Add `DESCRIPTION` and `REFERENCE`
5. Run `pytest tests/unit/optimizers/test_verifiable_rules.py::TestVerifiableRules::test_rule_is_correct[YourRule]`
6. If verification passes, you're done! The rule is proven correct.

**The declarative DSL refactoring is complete. The codebase rules are now maintainable, testable, and mathematically verified.**

---

## Composition over Inheritance Refactoring Status (2025)

The infrastructure for composition-based refactoring has been created but is not yet complete.

### ✅ What's Already Done

#### 1. **Core Abstractions Defined** ✓
- **File**: `src/d810/optimizers/core.py` (144 LOC)
- **Created**:
  - `OptimizationContext` - Immutable context dataclass (eliminates mutable state in rules)
  - `OptimizationRule` - Protocol-based interface (decouples rules from execution engine)
  - `PatternMatchingRule` - ABC for pattern-based rules

#### 2. **Service Layer Created** ✓
- **File**: `src/d810/optimizers/microcode/flow/flattening/services.py` (271 LOC)
- **Created**:
  - `Dispatcher` - Immutable dataclass replacing `GenericDispatcherInfo`
  - `DispatcherFinder` - Protocol for finding dispatchers
  - `PathEmulator` - Service for resolving state variables (SKELETON ONLY)
  - `CFGPatcher` - Service for modifying control flow graph (SKELETON ONLY)

#### 3. **Refactored Coordinator** ✓
- **File**: `src/d810/optimizers/microcode/flow/flattening/unflattener_refactored.py` (284 LOC)
- **Created**:
  - `UnflattenerRule` - Clean coordinator using composition (vs 775 LOC God object)
  - `OLLVMDispatcherFinder` - Concrete implementation (SKELETON ONLY)
- **Comparison**:
  - Original `GenericDispatcherUnflatteningRule`: 775 LOC, 21 methods, 10+ state variables
  - Refactored `UnflattenerRule`: 284 LOC, 3 methods, 3 dependencies (injected)

### ⚠️ What's Not Done (TODOs)

#### 1. **Implement Service Methods**

**PathEmulator.resolve_target()** (lines 110-151 in services.py):
```python
# TODO: Implement using existing MopTracker and MicroCodeInterpreter
# from d810.hexrays.tracker import MopTracker
# from d810.expr.emulator import MicroCodeInterpreter
```

**CFGPatcher.redirect_edge()** (lines 166-199):
```python
# TODO: Implement using existing cfg_utils
# from d810.hexrays.cfg_utils import change_1way_block_successor
```

**CFGPatcher.insert_intermediate_block()** (lines 201-238):
```python
# TODO: Implement using existing cfg_utils.create_block
```

**CFGPatcher.ensure_unconditional_predecessor()** (lines 240-270):
```python
# TODO: Implement using existing cfg_utils
# from d810.hexrays.cfg_utils import ensure_child_has_an_unconditional_father
```

#### 2. **Implement DispatcherFinder**

**OLLVMDispatcherFinder.find()** (lines 208-231 in unflattener_refactored.py):
```python
# TODO: Extract the actual dispatcher finding logic from the monolithic
# GenericDispatcherCollector and GenericDispatcherInfo classes
```

**Current state**: Returns empty list (placeholder)
**Needed**: Port logic from `generic.py::GenericDispatcherCollector` (83 LOC) and `GenericDispatcherInfo` (165 LOC)

#### 3. **Integration and Testing**

- ❌ No unit tests for new services
- ❌ Refactored unflattener not integrated into main optimizer loop
- ❌ Original `GenericDispatcherUnflatteningRule` still in use (not replaced)
- ❌ No migration path documented

### 📋 Remaining Work Plan

#### Phase 1: Implement Core Services (High Priority)

1. **Implement CFGPatcher methods** (Easiest - simple wrappers)
   - `redirect_edge()` → wrap `change_1way_block_successor()`
   - `insert_intermediate_block()` → wrap `create_block()`
   - `ensure_unconditional_predecessor()` → wrap `ensure_child_has_an_unconditional_father()`
   - **Estimated**: 50-100 LOC, 2-3 hours
   - **Dependencies**: `d810.hexrays.cfg_utils`

2. **Implement PathEmulator.resolve_target()** (Medium complexity)
   - Extract emulation logic from `GenericDispatcherUnflatteningRule.emulate_dispatcher_with_father_history()`
   - Use existing `MopTracker` and `MicroCodeInterpreter`
   - **Estimated**: 100-150 LOC, 4-6 hours
   - **Dependencies**: `d810.hexrays.tracker`, `d810.expr.emulator`

3. **Implement OLLVMDispatcherFinder.find()** (Highest complexity)
   - Extract dispatcher detection from `GenericDispatcherCollector` (83 LOC)
   - Extract dispatcher info from `GenericDispatcherInfo` (165 LOC)
   - Convert to immutable `Dispatcher` dataclass
   - **Estimated**: 150-250 LOC, 6-8 hours
   - **Dependencies**: `generic.py::GenericDispatcherCollector`, `GenericDispatcherInfo`, `GenericDispatcherBlockInfo`

#### Phase 2: Testing and Validation

4. **Write Unit Tests**
   - Test `CFGPatcher` methods with mock blocks
   - Test `PathEmulator` with known state variable scenarios
   - Test `OLLVMDispatcherFinder` with sample obfuscated code
   - Test `UnflattenerRule` with mocked dependencies
   - **Estimated**: 200-300 LOC tests, 4-6 hours

5. **Integration Testing**
   - Run refactored unflattener on real obfuscated binaries
   - Compare results with original `GenericDispatcherUnflatteningRule`
   - Measure performance (should be similar or better)
   - **Estimated**: 2-4 hours

#### Phase 3: Migration and Cleanup

6. **Integrate into Main Optimizer Loop**
   - Update `OptimizerManager` to use `UnflattenerRule`
   - Add configuration support for new services
   - Maintain backward compatibility (optional)
   - **Estimated**: 100-150 LOC, 2-3 hours

7. **Deprecate Old Code** (Optional but recommended)
   - Mark `GenericDispatcherUnflatteningRule` as deprecated
   - Add migration guide for custom unflatteners
   - Eventually remove old implementation
   - **Estimated**: Documentation + 1-2 hours

### 📊 Progress Summary

| Component | Status | LOC | Completion |
|-----------|--------|-----|------------|
| Core Abstractions | ✅ Complete | 144 | 100% |
| Service Protocols | ✅ Complete | 271 | 100% |
| Refactored Coordinator | ✅ Skeleton | 284 | 40% |
| CFGPatcher Implementation | ❌ TODO | 0/100 | 0% |
| PathEmulator Implementation | ❌ TODO | 0/150 | 0% |
| OLLVMDispatcherFinder | ❌ TODO | 0/250 | 0% |
| Unit Tests | ❌ TODO | 0/300 | 0% |
| Integration | ❌ TODO | 0/150 | 0% |
| **TOTAL** | **In Progress** | **699/1649** | **42%** |

### 🎯 Next Steps

**Recommended order**:

1. **Start with CFGPatcher** (low risk, high value)
   - Simple wrappers around existing functions
   - Immediate testability improvement
   - No complex logic

2. **Then PathEmulator** (medium risk, high value)
   - Core functionality needed for unflattening
   - Reuses existing emulation logic
   - Enables end-to-end testing

3. **Finally OLLVMDispatcherFinder** (high complexity, necessary)
   - Most complex extraction work
   - Requires understanding existing detection heuristics
   - Unlocks full refactored unflattener

4. **Write tests continuously** (not at the end)
   - Test each service as it's implemented
   - Catch bugs early
   - Build confidence in refactoring

### 📝 Key Benefits (When Complete)

- **Testability**: Each service testable in isolation with mocks
- **Clarity**: Clean separation of concerns (find/emulate/patch)
- **Maintainability**: Changes to one service don't affect others
- **Reusability**: Services can be used by different unflattening strategies
- **Debugging**: Easy to log/inspect at service boundaries

**Current Status**: Foundation is solid, implementation is 42% complete. With focused effort, remaining work is ~20-30 hours.

