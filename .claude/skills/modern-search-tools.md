# Modern Search Tools Skills

This skill covers the usage of `ast-grep` (`sg`), `fdfind` (`fd`), and `ripgrep` (`rg`). These tools are faster and more semantically aware than their traditional counterparts.

## 1. ast-grep (`sg`)
`ast-grep` performs structural search and replace based on the Abstract Syntax Tree (AST), making it far more powerful than regex for code.

- **Command:** `sg`
- **Key Flag:** `-p` (pattern), `-l` (language)
- **Pattern Syntax:** Use `$` followed by uppercase letters for metavariables (e.g., `$MATCH`).

### Usage Examples
*   **Find all console logs:**
    `sg search -p 'console.log($A)' -l javascript`
    *Matches `console.log("hello")`, `console.log(variable)`, etc.*

*   **Find function calls with specific arguments:**
    `sg search -p 'myFunction($A, "constant")' -l python`

*   **Refactoring Preview:**
    `sg search -p 'old_func($A)' --rewrite 'new_func($A)' -l python`
    *Use this to check matches before applying changes.*

## 2. fdfind (`fd`)
`fd` is a simple, fast, and user-friendly alternative to `find`.

- **Command:** `fd`
- **Usage:** `fd [pattern] [path]`

### Usage Examples
*   **Find files by name:**
    `fd pattern`
    *Finds files containing "pattern" in the name.*

*   **Find files by extension:**
    `fd -e py`
    *Finds all Python files.*

*   **Find files including hidden/ignored:**
    `fd -H -I pattern`
    *Searches hidden files and ignores `.gitignore`.*

*   **Execute command on results:**
    `fd -e jpg -x convert {} {.}.png`

## 3. ripgrep (`rg`)
`rg` is a line-oriented search tool that recursively searches the current directory for a regex pattern. It respects `.gitignore` by default.

- **Command:** `rg`
- **Usage:** `rg [pattern] [path]`

### Usage Examples
*   **Basic Text Search:**
    `rg "search_term"`

*   **Case Insensitive:**
    `rg -i "search_term"`

*   **Show Context:**
    `rg -C 5 "error_message"`
    *Shows 5 lines of context around the match.*

*   **Search Specific File Types:**
    `rg -t py "import os"`
    *Searches only Python files.*

*   **Search Only Filenames (like `fd` but with regex):**
    `rg -g "*.{js,ts}" "import"`

## Combined Workflows

**Workflow: Structural Refactoring**
1.  Use `fd` to locate the relevant files: `fd -e ts`
2.  Use `sg` to find the structural pattern: `sg search -p 'foo($A)'`
3.  Analyze the AST matches to ensure accuracy.

**Workflow: Deep Investigation**
1.  Use `rg` to find a specific error string: `rg "Connection failed"`
2.  Use `rg -C 10` on the specific file to read the surrounding code.
3.  Use `kit usages` (if available) on the function raising the error to see how it's called.
