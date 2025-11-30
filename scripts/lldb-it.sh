#!/bin/bash

# Find process and line number
IDA_PID=$(pgrep -x ida)
if [ -z "$IDA_PID" ]; then
    echo "Error: IDA process not found"
    exit 1
fi

LINE_NUM=$(rg -n "static PyObject \*__pyx_f_.*?_fast_ast_fast_minsn_to_ast.*?\)\s*\{" -i --glob '*.{c,cpp,cxx}' --no-heading | awk -F':' '{print $2}')
if [ -z "$LINE_NUM" ]; then
    echo "Error: Could not find target function"
    exit 1
fi

echo "Found IDA process: $IDA_PID"
echo "Found function at line: $LINE_NUM"
# Find all .dSYM files under ./src/d810 (including hidden and ignored)
DSYM_FILES=$(fd -u .dSYM ./src/d810)

# For each .dSYM file, add a target symbols add command (strip trailing / if present)
SYMBOL_COMMANDS=""
while IFS= read -r line; do
    # Remove trailing slash if present
    CLEANED_LINE="${line%/}"
    echo "target symbols add ${CLEANED_LINE}"
done <<< "$DSYM_FILES" > /tmp/lldb_symbols.txt

# Create command file
cat > /tmp/lldb_commands.txt << EOF
# breakpoint set --file _fast_ast.cpp --line ${LINE_NUM}
$(cat /tmp/lldb_symbols.txt)
breakpoint list
target list
continue
EOF

rm -f /tmp/lldb_symbols.txt

# Run LLDB with commands - this will execute the commands and then drop you into interactive mode
lldb -p "$IDA_PID" -s "/tmp/lldb_commands.txt"

# Clean up
rm -f /tmp/lldb_commands.txt