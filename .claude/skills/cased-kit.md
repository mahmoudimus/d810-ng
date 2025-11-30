# Cased Kit Skills

`kit` is a toolkit for codebase mapping, symbol extraction, and code search. Use it to quickly understand the structure and relationships within a repository.

## Core Commands

### 1. File Tree (`kit file-tree`)

Use this to get a high-level overview of the project structure.

- **Usage:** `kit file-tree [path]`
- **Example:** `kit file-tree .`
- **When to use:** At the start of a session to understand the project layout or when exploring a new directory.

### 2. Symbol Extraction (`kit symbols`)

Use this to list functions, classes, and other symbols defined in the code.

- **Usage:** `kit symbols [path]`
- **Example:** `kit symbols src/main.py`
- **When to use:** To find where specific logic resides without reading every line of code.

### 3. Code Search (`kit search`)

Use this to find code patterns.

- **Usage:** `kit search [path] "pattern"`
- **Example:** `kit search src "def main"`
- **When to use:** To locate specific definitions or patterns across the codebase.

### 4. Find Usages (`kit usages`)

Use this to find where a specific symbol (class, function, variable) is used.

- **Usage:** `kit usages [path] "SymbolName"`
- **Example:** `kit usages . "UserFactory"`
- **When to use:** When refactoring or trying to understand the impact of changing a specific component.

## Example Workflows

**Workflow: Mapping a New Codebase**

1. Run `kit file-tree .` to see the directory structure.
2. Identify key directories (e.g., `src`, `lib`).
3. Run `kit symbols src/` to see the main classes and functions.

**Workflow: Impact Analysis**

1. Identify the symbol you want to change (e.g., `process_data`).
2. Run `kit usages . "process_data"` to find all call sites.
3. Use `kit search` to find related comments or string references if necessary.
