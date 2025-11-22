#!/usr/bin/env python3
"""Proof-of-concept: Convert d810 rules to FOL specifications.

This demonstrates automated conversion for simple rules (Category 1).
"""

from __future__ import annotations
from dataclasses import dataclass
from typing import List, Union
from enum import Enum


# ============================================================================
# FOL DSL (minimal version for POC)
# ============================================================================

@dataclass(frozen=True)
class Var:
    name: str
    sort: str = "BitVec32"

@dataclass(frozen=True)
class Const:
    name: str
    value: int | None = None
    sort: str = "BitVec32"

class BvOp(Enum):
    ADD = "bvadd"
    SUB = "bvsub"
    MUL = "bvmul"
    AND = "bvand"
    OR = "bvor"
    XOR = "bvxor"
    NOT = "bvnot"
    NEG = "bvneg"
    SHL = "bvshl"
    LSHR = "bvlshr"
    ASHR = "bvashr"

@dataclass(frozen=True)
class BvExpr:
    op: BvOp
    args: List[Term]

    def __str__(self):
        if self.op == BvOp.NOT and len(self.args) == 1:
            return f"~{self.args[0]}"
        if self.op == BvOp.NEG and len(self.args) == 1:
            return f"-{self.args[0]}"
        if len(self.args) == 2:
            ops = {BvOp.ADD: "+", BvOp.SUB: "-", BvOp.MUL: "*",
                   BvOp.AND: "&", BvOp.OR: "|", BvOp.XOR: "^"}
            if self.op in ops:
                return f"({self.args[0]} {ops[self.op]} {self.args[1]})"
        return f"{self.op.value}({', '.join(map(str, self.args))})"

Term = Union[Var, Const, BvExpr]

@dataclass(frozen=True)
class BvEq:
    left: Term
    right: Term
    def __str__(self):
        return f"{self.left} == {self.right}"

@dataclass(frozen=True)
class Forall:
    vars: List[Var]
    body: Formula
    def __str__(self):
        var_list = ", ".join(v.name for v in self.vars)
        return f"∀{var_list}. ({self.body})"

Formula = Union[BvEq, Forall]

@dataclass(frozen=True)
class RuleSpec:
    name: str
    description: str
    correctness: Formula
    pattern: Term
    replacement: Term


# ============================================================================
# Converter: d810 AST -> FOL
# ============================================================================

def ast_to_fol(ast_node, ida_imports=None) -> Term:
    """Convert d810 AstNode to FOL Term.

    Args:
        ast_node: AstNode or AstLeaf from d810
        ida_imports: Dict mapping IDA opcodes to names (for matching)

    Returns:
        FOL Term representation
    """
    if ida_imports is None:
        # Default IDA opcode mappings
        import ida_hexrays
        ida_imports = {
            ida_hexrays.m_add: BvOp.ADD,
            ida_hexrays.m_sub: BvOp.SUB,
            ida_hexrays.m_mul: BvOp.MUL,
            ida_hexrays.m_and: BvOp.AND,
            ida_hexrays.m_or: BvOp.OR,
            ida_hexrays.m_xor: BvOp.XOR,
            ida_hexrays.m_bnot: BvOp.NOT,
            ida_hexrays.m_neg: BvOp.NEG,
            ida_hexrays.m_shl: BvOp.SHL,
            ida_hexrays.m_shr: BvOp.LSHR,
            ida_hexrays.m_sar: BvOp.ASHR,
        }

    # Handle leaf nodes
    if hasattr(ast_node, 'is_leaf') and ast_node.is_leaf():
        if hasattr(ast_node, 'is_constant') and ast_node.is_constant():
            # AstConstant
            value = getattr(ast_node, 'expected_value', None)
            return Const(ast_node.name, value)
        else:
            # AstLeaf (variable)
            return Var(ast_node.name)

    # Handle operator nodes
    if hasattr(ast_node, 'opcode'):
        op = ida_imports.get(ast_node.opcode)
        if op is None:
            raise ValueError(f"Unknown opcode: {ast_node.opcode}")

        # Convert children
        left = ast_to_fol(ast_node.left, ida_imports)

        # Unary operators
        if ast_node.right is None:
            return BvExpr(op, [left])

        # Binary operators
        right = ast_to_fol(ast_node.right, ida_imports)
        return BvExpr(op, [left, right])

    raise ValueError(f"Unknown AST node type: {type(ast_node)}")


def extract_vars(term: Term) -> List[Var]:
    """Extract all variables from a term (recursively)."""
    if isinstance(term, Var):
        return [term]
    elif isinstance(term, Const):
        return []
    elif isinstance(term, BvExpr):
        vars = []
        for arg in term.args:
            vars.extend(extract_vars(arg))
        # Deduplicate by name
        seen = set()
        unique = []
        for v in vars:
            if v.name not in seen:
                seen.add(v.name)
                unique.append(v)
        return unique
    return []


def convert_simple_rule(rule_class) -> RuleSpec:
    """Convert a simple d810 rule (Category 1: no constraints, no dynamic consts).

    Args:
        rule_class: VerifiableRule subclass

    Returns:
        RuleSpec with FOL correctness condition
    """
    # Instantiate the rule
    rule_instance = rule_class()

    # Get pattern and replacement
    pattern_ast = rule_instance.pattern.node
    replacement_ast = rule_instance.replacement.node

    # Convert to FOL
    pattern_fol = ast_to_fol(pattern_ast)
    replacement_fol = ast_to_fol(replacement_ast)

    # Extract unique variables
    pattern_vars = extract_vars(pattern_fol)
    replacement_vars = extract_vars(replacement_fol)

    # Combine and deduplicate
    all_vars = pattern_vars[:]
    for v in replacement_vars:
        if v.name not in [x.name for x in all_vars]:
            all_vars.append(v)

    # Build correctness formula
    correctness = Forall(
        vars=all_vars,
        body=BvEq(pattern_fol, replacement_fol)
    )

    # Get metadata
    name = rule_class.__name__
    description = getattr(rule_class, 'DESCRIPTION', 'No description')

    return RuleSpec(
        name=name,
        description=description,
        correctness=correctness,
        pattern=pattern_fol,
        replacement=replacement_fol
    )


# ============================================================================
# Demo: Convert actual d810 rules
# ============================================================================

if __name__ == "__main__":
    import sys
    sys.path.insert(0, "src")

    # Setup IDA environment
    try:
        import idapro
    except:
        pass

    # Import d810 rules
    from d810.optimizers.microcode.instructions.pattern_matching import rewrite_add_refactored

    # Convert some simple rules
    simple_rules = [
        rewrite_add_refactored.Add_HackersDelightRule_1,
        rewrite_add_refactored.Add_HackersDelightRule_2,
        rewrite_add_refactored.Add_HackersDelightRule_3,
        rewrite_add_refactored.Add_HackersDelightRule_4,
        rewrite_add_refactored.Add_HackersDelightRule_5,
        rewrite_add_refactored.Add_OllvmRule_1,
        rewrite_add_refactored.Add_OllvmRule_3,
    ]

    print("="*70)
    print("D810 -> FOL Conversion Proof-of-Concept")
    print("="*70)
    print()

    for rule_cls in simple_rules:
        print(f"Converting: {rule_cls.__name__}")
        print("-" * 70)

        try:
            spec = convert_simple_rule(rule_cls)

            print(f"Name:        {spec.name}")
            print(f"Description: {spec.description}")
            print()
            print(f"Correctness: {spec.correctness}")
            print()
            print(f"Pattern:     {spec.pattern}")
            print(f"Replacement: {spec.replacement}")
            print()

            # Could verify here with: verify(spec)

        except Exception as e:
            print(f"ERROR: {e}")
            import traceback
            traceback.print_exc()

        print("="*70)
        print()
