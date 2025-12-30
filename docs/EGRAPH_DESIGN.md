# E-graph Integration with MBA Rules

## Executive Summary

E-graphs (equality graphs) would dramatically improve d810's MBA deobfuscation by:
1. **Automatic chain discovery** - Find multi-step simplifications in one pass
2. **Bidirectional rewrites** - Explore all equivalent forms, not just simplification
3. **Optimality guarantees** - Saturation proves we found the simplest form
4. **Subexpression sharing** - Automatically handle common subexpressions

The MBA package is **already well-positioned** for e-graph integration thanks to:
- Pure `SymbolicExpression` DSL (no IDA dependencies)
- Z3-verified rules (guaranteed semantically correct)
- Standalone `d810.mba` package (can use with egg-python or custom implementation)

## Background: E-graphs for Optimization

E-graphs are a data structure that compactly represents many equivalent expressions simultaneously. They're used in modern optimizers (like `egg` in Rust, `egglog`) to:

1. **Find all equivalent forms** - Not just one pattern match, but discover chains of rewrites
2. **Avoid infinite loops** - Track which rewrites have been tried
3. **Cost-based selection** - Choose the "best" equivalent form based on a cost function
4. **Saturation** - Apply all rewrites until no new equivalences are found

### Example: Why E-graphs Beat Pattern Matching

**Obfuscated expression:**
```
((x + y) - 2*(x & y) | z) - ((x + y) - 2*(x & y) & z)
```

**Current pattern matching approach:**
- Rule 1: `(x + y) - 2*(x & y) => x ^ y` doesn't match (outer ops are | and -)
- Rule 2: `(a | b) - (a & b) => a ^ b` doesn't match (a would need to be simplified first)
- Result: ❌ No simplification (need multiple passes, careful rule ordering)

**E-graph approach:**
1. Add both rules as **bidirectional** rewrites
2. Saturate: automatically discover that `(x+y)-2*(x&y)` appears twice
3. Add `x^y` to the same e-class (equivalence class)
4. Now see `(x^y | z) - (x^y & z)` → matches Rule 2!
5. Final form: `x ^ y ^ z` (5 nodes vs 17 nodes)
6. Result: ✅ Optimal simplification in one pass

## Current MBA Architecture

```python
# d810/mba/verifier.py
class MBARule(abc.ABC):
    name: str
    description: str

    @property
    @abc.abstractmethod
    def pattern(self) -> SymbolicExpression:
        """The pattern to match."""
        ...

    @property
    @abc.abstractmethod
    def replacement(self) -> SymbolicExpression:
        """The replacement expression."""
        ...

    def verify(self) -> bool:
        """Z3 proves PATTERN ≡ REPLACEMENT."""
        return prove_equivalence(self.pattern, self.replacement)
```

**Key advantage:** Rules are already `SymbolicExpression` objects with Z3 verification!

## E-graph Extension Design

### Architecture Overview

```
d810.mba (IDA-independent)
├── dsl.py               ← SymbolicExpression (already perfect for e-graphs!)
├── verifier.py          ← MBARule (Z3-verified rewrites)
└── egraph.py            ← NEW: E-graph integration
    ├── MBARuleset       ← Collection of verified rules
    ├── EGraphSimplifier ← Standalone simplifier (no IDA)
    └── EGraphBackend    ← Protocol for egg-python/custom impl

d810.optimizers (IDA-dependent)
└── microcode/
    └── egraph_optimizer.py  ← NEW: IDA microcode + e-graph
        └── EGraphMBAOptimizer ← minsn_t → SymbolicExpression → optimize → minsn_t
```

### Option 1: Standalone E-graph Simplifier (Recommended)

Pure Python, no IDA dependencies. Can be used in standalone MBA tools.

```python
# d810/mba/egraph.py

from typing import Protocol, Callable
from d810.mba.dsl import SymbolicExpression
from d810.mba.verifier import MBARule

class EGraphBackend(Protocol):
    """Protocol for e-graph implementations (egg-python, custom, etc.)"""

    def add(self, expr: SymbolicExpression) -> EClass: ...
    def add_rewrite(self, lhs: SymbolicExpression, rhs: SymbolicExpression): ...
    def saturate(self, max_iter: int = 100): ...
    def extract(self, eclass: EClass, cost_fn: Callable) -> SymbolicExpression: ...

class MBARuleset:
    """Collection of MBA rules for e-graph optimization."""

    def __init__(self, rules: list[MBARule]):
        self.rules = rules
        self._verified = set()

    def verify_all(self):
        """Verify all rules before using in e-graph."""
        for rule in self.rules:
            rule.verify()  # Z3 proves correctness
            self._verified.add(rule.name)

    def to_egraph_rewrites(self, bidirectional: bool = True) -> list[tuple[SymbolicExpression, SymbolicExpression]]:
        """Convert rules to e-graph rewrites.

        Args:
            bidirectional: If True, add both pattern→replacement and replacement→pattern.
                          Most MBA identities are bidirectional.
        """
        rewrites = []

        for rule in self.rules:
            # Add forward rewrite
            rewrites.append((rule.pattern, rule.replacement))

            # Add backward rewrite (most MBA rules are bidirectional)
            if bidirectional:
                rewrites.append((rule.replacement, rule.pattern))

        return rewrites

class EGraphSimplifier:
    """Simplify MBA expressions using e-graph saturation."""

    def __init__(self, ruleset: MBARuleset, backend: EGraphBackend):
        self.ruleset = ruleset
        self.egraph = backend

        # Verify all rules with Z3
        self.ruleset.verify_all()

        # Load rewrites into e-graph
        for lhs, rhs in self.ruleset.to_egraph_rewrites():
            self.egraph.add_rewrite(lhs, rhs)

    def simplify(self, expr: SymbolicExpression) -> SymbolicExpression:
        """Find simplest equivalent expression."""
        eclass = self.egraph.add(expr)
        self.egraph.saturate(max_iter=100)
        return self.egraph.extract(eclass, cost_fn=self._cost)

    def _cost(self, expr: SymbolicExpression) -> int:
        """Cost function for extraction.

        Lower cost = better. Prefers simpler expressions.
        """
        cost = expr.ast_size()  # Base cost: number of nodes

        # Prefer XOR over MBA obfuscation
        if expr.operation == 'xor':
            cost -= 5

        # Penalize complex MBA patterns
        if expr.operation in ['add', 'sub'] and self._looks_like_mba(expr):
            cost += 10

        return cost

    def _looks_like_mba(self, expr: SymbolicExpression) -> bool:
        """Heuristic: detect MBA obfuscation patterns."""
        # Example: (x + y) - 2*(x & y) has both arithmetic and bitwise
        return (expr.has_arithmetic_ops() and expr.has_bitwise_ops())
```

### Option 2: IDA Integration (Hybrid Approach)

Use e-graphs within d810's microcode optimization pipeline.

```python
# d810/optimizers/microcode/egraph_optimizer.py

from d810.mba.egraph import MBARuleset, EGraphSimplifier
from d810.optimizers.rules import RULE_REGISTRY

class EGraphMBAOptimizer:
    """Optimize IDA microcode using e-graph saturation."""

    def __init__(self):
        # Use existing verified MBA rules
        ruleset = MBARuleset(RULE_REGISTRY)
        self.simplifier = EGraphSimplifier(ruleset, backend=EggBackend())

    def optimize_instruction(self, ins: minsn_t) -> Optional[minsn_t]:
        """Optimize a single microcode instruction."""

        # Phase 1: Convert IDA minsn_t to SymbolicExpression
        expr = self._minsn_to_symbolic(ins)
        if expr is None:
            return None

        # Phase 2: E-graph optimization
        optimized = self.simplifier.simplify(expr)

        # Phase 3: Convert back to minsn_t
        if optimized != expr and self._is_better(optimized, expr):
            return self._symbolic_to_minsn(optimized, ins)

        return None

    def optimize_block(self, blk: mblock_t) -> int:
        """Optimize entire basic block (handles cross-instruction patterns)."""

        # Build e-graph from all instructions in block
        egraph = self._build_block_egraph(blk)

        # Saturate
        egraph.saturate()

        # Extract optimized instructions
        return self._apply_optimizations(blk, egraph)

    def _minsn_to_symbolic(self, ins: minsn_t) -> SymbolicExpression:
        """Convert IDA microcode to symbolic expression."""
        # Use existing d810 AST → SymbolicExpression conversion
        ...

    def _symbolic_to_minsn(self, expr: SymbolicExpression, template: minsn_t) -> minsn_t:
        """Convert symbolic expression back to IDA microcode."""
        # Use existing SymbolicExpression → AST → minsn_t conversion
        ...
```

## Extension Points for MBA Rules

To support e-graphs, extend `MBARule` with optional e-graph metadata:

```python
# d810/mba/verifier.py

class MBARule(abc.ABC):
    # Existing
    name: str
    description: str

    @property
    @abc.abstractmethod
    def pattern(self) -> SymbolicExpression: ...

    @property
    @abc.abstractmethod
    def replacement(self) -> SymbolicExpression: ...

    def verify(self) -> bool: ...

    # New: E-graph support (optional)
    BIDIRECTIONAL: bool = True  # Most MBA identities are bidirectional
    COST_PREFERENCE: int = 0     # Hint for cost function (-1 = prefer pattern, +1 = prefer replacement)

    def is_bidirectional(self) -> bool:
        """Check if this rule is semantically bidirectional.

        Most MBA identities are bidirectional:
            x ^ y ≡ (x | y) - (x & y)  (both directions valid)

        But some are not:
            x + 0 => x  (one direction only - don't expand x to x+0)
            x * 1 => x  (simplification only)
        """
        return self.BIDIRECTIONAL

    def cost_delta(self) -> int:
        """Estimated cost change of applying this rule.

        Negative = simplification (reduces AST size)
        Positive = expansion (increases AST size)
        Zero = neutral rewrite

        Example:
            pattern = (x | y) - (x & y)  # 7 nodes
            replacement = x ^ y           # 3 nodes
            cost_delta = -4               # Saves 4 nodes
        """
        return self.replacement.ast_size() - self.pattern.ast_size()
```

### Adding `ast_size()` to SymbolicExpression

```python
# d810/mba/dsl.py

class SymbolicExpression:
    # Existing methods...

    def ast_size(self) -> int:
        """Count nodes in expression tree (for cost computation).

        Returns:
            Number of nodes (variables, constants, and operations).

        Example:
            x ^ y => 3 (x + y + xor)
            (x | y) - (x & y) => 7 (x + y + or + x + y + and + sub)
        """
        if self.is_leaf():
            return 1

        left_size = self.left.ast_size() if self.left else 0
        right_size = self.right.ast_size() if self.right else 0
        return 1 + left_size + right_size  # 1 for operation node
```

## Usage Example

```python
from d810.mba import Var, MBARule
from d810.mba.egraph import MBARuleset, EGraphSimplifier

# 1. Define MBA rules (or use existing RULE_REGISTRY)
x, y, z = Var("x"), Var("y"), Var("z")

class XorRule1(MBARule):
    name = "XOR from OR/AND"
    description = "Simplify (x|y)-(x&y) to x^y"
    pattern = (x | y) - (x & y)
    replacement = x ^ y
    BIDIRECTIONAL = True

class XorRule2(MBARule):
    name = "XOR from addition"
    description = "Simplify (x+y)-2*(x&y) to x^y"
    pattern = (x + y) - 2 * (x & y)
    replacement = x ^ y
    BIDIRECTIONAL = True

# 2. Create ruleset and verify
ruleset = MBARuleset([XorRule1(), XorRule2()])
ruleset.verify_all()  # Z3 proves all rules correct

# 3. Create e-graph simplifier
simplifier = EGraphSimplifier(ruleset, backend=EggBackend())

# 4. Simplify complex nested MBA
complex = ((x + y) - 2 * (x & y) | z) - ((x + y) - 2 * (x & y) & z)
simple = simplifier.simplify(complex)

print(f"Original:   {complex}")  # ((x+y)-2*(x&y) | z) - ((x+y)-2*(x&y) & z)
print(f"Simplified: {simple}")   # x ^ y ^ z
print(f"Cost saved: {complex.ast_size() - simple.ast_size()} nodes")  # 12 nodes saved
```

## Real-World d810 Example

**Obfuscated binary:**
```c
// Original code (decompiler shows)
uint64_t obfuscated(uint64_t rax, uint64_t rbx, uint64_t rcx) {
    uint64_t t1 = (rax | rbx) - (rax & rbx);       // Line 1
    uint64_t t2 = (t1 + rcx) - 2*(t1 & rcx);       // Line 2
    uint64_t rdx = (t2 | 1) - (t2 & 1);            // Line 3
    return rdx;
}
```

**Current d810 (pattern matching):**
- Pass 1: Simplify line 1: `t1 = rax ^ rbx`
- Pass 2: Simplify line 2: `t2 = t1 ^ rcx` → `t2 = rax ^ rbx ^ rcx`
- Pass 3: Simplify line 3: `rdx = t2 ^ 1` → `rdx = rax ^ rbx ^ rcx ^ 1`
- **Total: 3 passes needed**

**With E-graphs:**
- Add all 3 instructions to e-graph
- Saturate with MBA rules
- Extract optimal form: `rdx = rax ^ rbx ^ rcx ^ 1`
- **Total: 1 pass, guaranteed optimal**

**Deobfuscated:**
```c
uint64_t deobfuscated(uint64_t rax, uint64_t rbx, uint64_t rcx) {
    return rax ^ rbx ^ rcx ^ 1;  // Clean XOR chain
}
```

## Implementation Phases

### Phase 1: Add E-graph Support to MBA (2-4 hours)

**Files to modify:**
- `d810/mba/dsl.py` - Add `ast_size()` method
- `d810/mba/verifier.py` - Add `BIDIRECTIONAL`, `is_bidirectional()`, `cost_delta()`

**Testing:**
```python
# Test ast_size
x, y = Var("x"), Var("y")
assert (x ^ y).ast_size() == 3
assert ((x | y) - (x & y)).ast_size() == 7

# Test cost_delta
rule = XorRule1()
assert rule.cost_delta() == -4  # Saves 4 nodes
```

### Phase 2: Create E-graph Module (4-6 hours)

**New file:** `d810/mba/egraph.py`

**Dependencies:**
- Option A: Use `egg-python` (Python bindings for Rust egg library)
- Option B: Use `egglog-python` (Python implementation)
- Option C: Implement minimal custom e-graph (500-1000 LOC)

**Classes to implement:**
- `EGraphBackend` (Protocol)
- `MBARuleset` (ruleset management)
- `EGraphSimplifier` (standalone simplifier)

**Testing:**
- Unit tests: Verify simple rewrites work
- Integration tests: Verify chain discovery works
- Benchmark: Compare against pattern matching

### Phase 3: IDA Integration (6-8 hours)

**New file:** `d810/optimizers/microcode/egraph_optimizer.py`

**Integration points:**
- Convert `minsn_t` → `SymbolicExpression` (reuse existing code)
- Convert `SymbolicExpression` → `minsn_t` (new, ~200 LOC)
- Block-level optimization (handle cross-instruction patterns)

**Testing:**
- Test on real obfuscated binaries
- Compare deobfuscation quality vs current d810
- Measure performance (e-graphs are fast but have overhead)

### Phase 4: Advanced Features (Optional, 8-12 hours)

**Cost function customization:**
- Prefer operations with faster execution (XOR vs MUL)
- Prefer operations with fewer side effects
- Prefer shorter instruction encodings (x86 perspective)

**E-class analysis:**
- Track expression properties through rewrites
- Example: "this e-class always produces even numbers"
- Can enable conditional rewrites

**Visualization:**
- Export e-graph to GraphViz
- Show equivalence classes and rewrites
- Useful for debugging and papers

## Benefits Summary

### For d810 Users
1. **Better deobfuscation** - Finds more simplifications automatically
2. **Fewer passes needed** - One saturation vs multiple pattern matching passes
3. **Handles complex patterns** - Cross-instruction, common subexpressions
4. **Optimality guarantee** - Saturation proves we found the simplest form

### For d810 Developers
1. **Simpler rule authoring** - No need to worry about rule ordering
2. **Easier debugging** - E-graph shows all equivalent forms
3. **Better testing** - Can verify completeness (did we saturate?)
4. **Research opportunities** - E-graphs + MBA is novel combination

### For the Community
1. **Reusable framework** - `d810.mba.egraph` works standalone
2. **Publication potential** - "E-graphs for Binary Deobfuscation"
3. **Educational value** - Great example of formal methods in RE

## Open Questions

1. **Which e-graph backend?**
   - `egg-python`: Fast (Rust), mature, but requires Rust toolchain
   - `egglog-python`: Pure Python, but may be slower
   - Custom: Full control, but more work

2. **Cost function tuning?**
   - AST size is good default, but can we do better?
   - Should we consider x86 instruction encodings?
   - Should we prefer memory-safe operations?

3. **Cross-basic-block optimization?**
   - E-graphs can handle it, but is it worth the complexity?
   - Would need dataflow analysis to be sound

4. **Integration with existing optimizers?**
   - Should e-graphs replace pattern matching, or complement it?
   - Hybrid approach: pattern matching first, then e-graphs?

## References

- [egg: Fast and Extensible E-graphs](https://egraphs-good.github.io/)
- [egglog: E-graphs with Datalog](https://github.com/egraphs-good/egglog)
- [MBA Deobfuscation Papers](https://pldi24.sigplan.org/details/egraphs-2024-papers/6/Guided-Equality-Saturation)
- [Hex-Rays Microcode](https://hex-rays.com/products/decompiler/manual/sdk/hexrays.html)
