#!/usr/bin/env python3
"""Automated migration of DynamicConst to declarative constraints.

This script migrates remaining DynamicConst usages to the new declarative DSL.
"""

import re
import sys

def migrate_simple_bnot(content):
    """Migrate ~ctx["c_1"].value patterns."""
    # Pattern: DynamicConst("bnot_c_1", lambda ctx: ~ctx["c_1"].value, ...)
    pattern = r'(\s+)(\w+) = DynamicConst\("(\w+)", lambda ctx: ~ctx\["(\w+)"\]\.value.*?\)'

    matches = list(re.finditer(pattern, content))
    for match in reversed(matches):  # Reverse to maintain positions
        indent = match.group(1)
        var_name = match.group(2)
        const_name = match.group(3)
        source_const = match.group(4)

        # Replace with simple Const declaration
        replacement = f'{indent}{var_name} = Const("{const_name}")'
        content = content[:match.start()] + replacement + content[match.end():]

        print(f"  Migrated: {var_name} = ~{source_const}")

    return content

def migrate_simple_addition(content):
    """Migrate ctx["c_1"].value + N patterns."""
    # Pattern: DynamicConst("name", lambda ctx: ctx["c_X"].value + N, ...)
    pattern = r'(\s+)(\w+) = DynamicConst\("(\w+)", lambda ctx: ctx\["(\w+)"\]\.value \+ (\d+).*?\)'

    matches = list(re.finditer(pattern, content))
    for match in reversed(matches):
        indent = match.group(1)
        var_name = match.group(2)
        const_name = match.group(3)
        source_const = match.group(4)
        addend = match.group(5)

        # Replace with Const declaration
        replacement = f'{indent}{var_name} = Const("{const_name}")  # {source_const} + {addend}'
        content = content[:match.start()] + replacement + content[match.end():]

        print(f"  Migrated: {var_name} = {source_const} + {addend}")

    return content

def migrate_when_is_bnot(content):
    """Convert when.is_bnot("c_1", "c_2") to c_1 == ~c_2."""
    pattern = r'when\.is_bnot\("(\w+)", "(\w+)"\)'

    def replacer(match):
        c1, c2 = match.groups()
        return f'{c1} == ~{c2}'

    new_content = re.sub(pattern, replacer, content)

    if new_content != content:
        count = len(re.findall(pattern, content))
        print(f"  Converted {count} when.is_bnot() to declarative constraints")

    return new_content

def remove_dynamic_const_import(content):
    """Remove DynamicConst from imports."""
    content = re.sub(r', DynamicConst(?=\s|$)', '', content)
    content = re.sub(r'DynamicConst, ', '', content)
    return content

def main():
    """Process a file and migrate DynamicConst usages."""
    if len(sys.argv) < 2:
        print("Usage: migrate_dynamic_const.py <file>")
        sys.exit(1)

    filename = sys.argv[1]

    print(f"Migrating {filename}...")

    with open(filename, 'r') as f:
        content = f.read()

    # Apply migrations
    content = migrate_when_is_bnot(content)
    content = migrate_simple_bnot(content)
    content = migrate_simple_addition(content)
    content = remove_dynamic_const_import(content)

    with open(filename, 'w') as f:
        f.write(content)

    print(f"  ✓ Migration complete")

if __name__ == "__main__":
    main()
