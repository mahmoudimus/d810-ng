#!/usr/bin/env python3
"""Bulk migrate CST file DynamicConst usages."""

import re

# Read the file
with open('src/d810/optimizers/microcode/instructions/pattern_matching/rewrite_cst_refactored.py', 'r') as f:
    content = f.read()

# Migration 1: c_res = ctx["c_1"].value & ctx["c_2"].value
# Replace with: c_res = Const("c_res") + constraint c_res == c_1 & c_2
content = re.sub(
    r'c_res = DynamicConst\(\s*"c_res",\s*lambda ctx: ctx\["c_1"\]\.value & ctx\["c_2"\]\.value.*?\)',
    'c_res = Const("c_res")  # c_1 & c_2',
    content,
    flags=re.DOTALL
)

# Migration 2: c_res = ctx["c_1"].value >> ctx["c_2"].value
content = re.sub(
    r'c_res = DynamicConst\(\s*"c_res",\s*lambda ctx: ctx\["c_1"\]\.value >> ctx\["c_2"\]\.value.*?\)',
    'c_res = Const("c_res")  # c_1 >> c_2',
    content,
    flags=re.DOTALL
)

# Migration 3: c_res = ctx["c_1"].value << ctx["c_2"].value
content = re.sub(
    r'c_res = DynamicConst\(\s*"c_res",\s*lambda ctx: ctx\["c_1"\]\.value << ctx\["c_2"\]\.value.*?\)',
    'c_res = Const("c_res")  # c_1 << c_2',
    content,
    flags=re.DOTALL
)

# Migration 4: bnot_c_1 = ~ctx["c_1"].value
content = re.sub(
    r'bnot_c_1 = DynamicConst\(\s*"bnot_c_1",\s*lambda ctx: ~ctx\["c_1"\]\.value.*?\)',
    'bnot_c_1 = Const("bnot_c_1")  # ~c_1',
    content,
    flags=re.DOTALL
)

# Migration 5: c_1_bnot = ~ctx["c_1"].value
content = re.sub(
    r'c_1_bnot = DynamicConst\(\s*"c_1_bnot",\s*lambda ctx: ~ctx\["c_1"\]\.value.*?\)',
    'c_1_bnot = Const("c_1_bnot")  # ~c_1',
    content,
    flags=re.DOTALL
)

# Migration 6: not_cst_1 = ~ctx["cst_1"].value
content = re.sub(
    r'not_cst_1 = DynamicConst\(\s*"not_cst_1",\s*lambda ctx: ~ctx\["cst_1"\]\.value.*?\)',
    'not_cst_1 = Const("not_cst_1")  # ~cst_1',
    content,
    flags=re.DOTALL
)

# Migration 7: lnot_c_1 = 1 if ctx["c_1"].value == 0 else 0
content = re.sub(
    r'lnot_c_1 = DynamicConst\(\s*"lnot_c_1",\s*lambda ctx: 1 if ctx\["c_1"\]\.value == 0 else 0.*?\)',
    'lnot_c_1 = Const("lnot_c_1")  # logical NOT of c_1',
    content,
    flags=re.DOTALL
)

# Migration 8: c_and/c_xor pairs
content = re.sub(
    r'c_and = DynamicConst\(\s*"c_and",\s*lambda ctx: ctx\["c_1"\]\.value & ctx\["c_2"\]\.value.*?\)',
    'c_and = Const("c_and")  # c_1 & c_2',
    content,
    flags=re.DOTALL
)

content = re.sub(
    r'c_xor = DynamicConst\(\s*"c_xor",\s*lambda ctx: ctx\["c_1"\]\.value \^ ctx\["c_2"\]\.value.*?\)',
    'c_xor = Const("c_xor")  # c_1 ^ c_2',
    content,
    flags=re.DOTALL
)

# Migration 9: c_diff = ctx["c_1"].value - ctx["c_2"].value
content = re.sub(
    r'c_diff = DynamicConst\(\s*"c_diff",\s*lambda ctx: ctx\["c_1"\]\.value - ctx\["c_2"\]\.value.*?\)',
    'c_diff = Const("c_diff")  # c_1 - c_2',
    content,
    flags=re.DOTALL
)

# Migration 10: c_and_res/c_xor_res
content = re.sub(
    r'c_and_res = DynamicConst\(\s*"c_and_res",\s*lambda ctx: ctx\["c_and_1"\]\.value & ctx\["c_and_2"\]\.value.*?\)',
    'c_and_res = Const("c_and_res")  # c_and_1 & c_and_2',
    content,
    flags=re.DOTALL
)

content = re.sub(
    r'c_xor_res = DynamicConst\(\s*"c_xor_res",\s*lambda ctx: ctx\["c_xor_1"\]\.value \^ ctx\["c_xor_2"\]\.value.*?\)',
    'c_xor_res = Const("c_xor_res")  # c_xor_1 ^ c_xor_2',
    content,
    flags=re.DOTALL
)

# Write back
with open('src/d810/optimizers/microcode/instructions/pattern_matching/rewrite_cst_refactored.py', 'w') as f:
    f.write(content)

print("✓ Bulk migrations applied")
print(f"Remaining DynamicConst: {content.count('DynamicConst(')}")
