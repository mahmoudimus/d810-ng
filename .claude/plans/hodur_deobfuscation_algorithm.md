# Hodur Deobfuscation Algorithm - Manual Symbolic Trace

**Date**: 2025-11-28
**Target**: `_hodur_func` in `samples/src/c/hodur_c2_flattened.c`

## Manual Symbolic Execution

### Step 1: Identify the State Variable

```c
int32_t state = -1292005450;  // 0xB2FD8FB6 (unsigned)
```

**Detection heuristics:**
- Variable assigned a large constant (> 0x10000) early in function
- Same variable compared in multiple `if` statements
- Variable reassigned inside each state handler

### Step 2: Extract All State Constants

Tracing through the code, we find 14 unique states:

| State (Hex) | State (Signed) | Purpose |
|-------------|----------------|---------|
| 0xB2FD8FB6 | -1292005450 | INITIAL - Decrypt WinHttpSetOption (Algo 1) |
| 0xC6685257 | -967085481 | Resolve & call WinHttpSetOption (Connect Timeout) |
| 0xB92456DE | -1188669218 | Decrypt WinHttpSetOption (Algo 2) |
| 0x3C8960A9 | 1015832745 | Resolve & call WinHttpSetOption (Receive Timeout) |
| 0xEC031199 | -335540839 | Decrypt WinHttpSetOption (Algo 3) |
| 0x87A0CA6E | -2019657106 | Resolve & call WinHttpSetOption (Send Timeout) |
| 0xB7F8A88B | -1208444789 | Decrypt WinHttpOpenRequest |
| 0x0B8148F6 | 193431798 | Resolve & call WinHttpOpenRequest |
| 0xB86ECBE0 | -1184359456 | Decrypt WinHttpSendRequest |
| 0x16DA1DAC | 383589804 | Resolve & call WinHttpSendRequest |
| 0x4E4A2BBD | 1313369021 | Decrypt WinHttpReceiveResponse |
| 0xD62B0F79 | -702087303 | Resolve & call WinHttpReceiveResponse |
| 0xD46D65DC | -731028004 | ERROR - Break from loop |
| 0xB2D8EADE | -1294705954 | END - Success, break from loop |

### Step 3: Build State Transition Graph

```
INITIAL (0xB2FD8FB6)
    │
    ▼
0xC6685257  ──────────────────────────────────────────┐
    │                                                  │
    ▼                                                  │
0xB92456DE                                             │
    │                                                  │
    ▼                                                  │
0x3C8960A9                                             │
    │                                                  │
    ▼                                                  │
0xEC031199                                             │
    │                                                  │
    ▼                                                  │
0x87A0CA6E                                             │
    │                                                  │
    ▼                                                  │
0xB7F8A88B                                             │
    │                                                  │
    ▼                                                  │
0x0B8148F6                                             │
    │                                                  │
    ├──── (hRequest == NULL) ───► 0xD46D65DC (ERROR) ──┤
    │                                                  │
    ▼                                                  │
0xB86ECBE0                                             │
    │                                                  │
    ▼                                                  │
0x16DA1DAC                                             │
    │                                                  │
    ├──── (!res) ───────────────► 0xD46D65DC (ERROR) ──┤
    │                                                  │
    ▼                                                  │
0x4E4A2BBD                                             │
    │                                                  │
    ▼                                                  │
0xD62B0F79                                             │
    │                                                  │
    ▼                                                  │
0xB2D8EADE (END)                                       │
    │                                                  │
    ▼                                                  ▼
  break                                              break
```

### Step 4: Identify Transition Types

**Unconditional transitions** (12 total):
- 0xB2FD8FB6 → 0xC6685257
- 0xC6685257 → 0xB92456DE
- 0xB92456DE → 0x3C8960A9
- 0x3C8960A9 → 0xEC031199
- 0xEC031199 → 0x87A0CA6E
- 0x87A0CA6E → 0xB7F8A88B
- 0xB7F8A88B → 0x0B8148F6
- 0xB86ECBE0 → 0x16DA1DAC
- 0x4E4A2BBD → 0xD62B0F79
- 0xD62B0F79 → 0xB2D8EADE
- 0xD46D65DC → break
- 0xB2D8EADE → break

**Conditional transitions** (2 total):
- 0x0B8148F6 → 0xB86ECBE0 (if hRequest != NULL) OR 0xD46D65DC (if hRequest == NULL)
- 0x16DA1DAC → 0x4E4A2BBD (if res) OR 0xD46D65DC (if !res)

---

## The 5-Phase Deobfuscation Algorithm

### Phase 1: State Variable Detection

**Goal**: Find the dispatch variable

**Algorithm**:
1. Scan all blocks for conditional jumps (jnz, jz) comparing against large constants (> 0x10000)
2. Group by the operand being compared (left side of comparison)
3. The operand compared most frequently is the state variable
4. Validate: same operand should also appear in assignments (mov)

**In microcode**:
```
jnz %var_118.4, 0xB2FD8FB6, block_X   ; state check
mov %var_118.4, 0xC6685257            ; state assignment
```

The state variable is `%var_118.4` (stack offset -0x118, 4 bytes).

### Phase 2: State Constant Collection

**Goal**: Find all state values

**Algorithm**:
1. Find all comparisons against the state variable → get comparison constants
2. Find all assignments to the state variable → get assignment constants
3. Union both sets → complete state constant set
4. Identify initial state: first assignment in entry block or early blocks

**Result for hodur_func**: 14 constants as listed above

### Phase 3: State Handler Mapping

**Goal**: Map each state constant to its handler code

**Algorithm**:
1. For each state check block `jnz state, CONST, target`:
   - The **fall-through** path (when state == CONST) is the handler
   - The **jump target** is the next state check (or loop exit)
2. BFS from fall-through to find all handler blocks until:
   - We hit another state check block
   - We hit a state assignment (transition point)

**Handler structure**:
```
[State Check: jnz state, 0xB2FD8FB6]
        │
        ├── (state != 0xB2FD8FB6) → next state check
        │
        ▼ (state == 0xB2FD8FB6)
   [Handler blocks...]
        │
        ▼
   [State Assignment: mov state, 0xC6685257]
        │
        ▼
   [Jump back to dispatcher]
```

### Phase 4: Transition Graph Construction

**Goal**: Build edges between state handlers

**Algorithm**:
1. For each handler, find state assignments within it
2. Each assignment `mov state, NEXT_CONST` creates edge: `CURRENT_STATE → NEXT_STATE`
3. Handle conditional transitions:
   - If assignment is inside a conditional (if/else), mark edge as conditional
   - Track the condition that guards the assignment

**Data structure**:
```python
@dataclass
class StateTransition:
    from_state: int
    to_state: int
    from_block: int           # Block where assignment occurs
    is_conditional: bool
    condition: str | None     # e.g., "hRequest != NULL"
```

### Phase 5: CFG Reconstruction (Patching)

**Goal**: Replace state machine with direct control flow

**Algorithm**:
For each predecessor of a state check block:
1. Track state variable backward from predecessor
2. Determine which state value the predecessor has
3. Based on the state value:
   - If state == CHECK_CONST: redirect predecessor to handler (fall-through)
   - If state != CHECK_CONST: redirect predecessor to next check (jump target)
4. Create duplicate blocks to preserve CFG for other predecessors

**Patching strategy** (same as FixPredecessorOfConditionalJumpBlock):
```python
# For predecessor that always matches (state == CONST):
new_block = duplicate_block(check_block)
make_goto(new_block, handler_block)  # Skip the check
redirect(predecessor, check_block → new_block)

# For predecessor that never matches (state != CONST):
new_block = duplicate_block(check_block)
make_goto(new_block, next_check_block)  # Skip to next check
redirect(predecessor, check_block → new_block)
```

---

## Correctness Verification

After deobfuscation, the reconstructed CFG should:

1. **Preserve all handler code**: Every state handler's code must be reachable
2. **Preserve control flow semantics**: Conditional transitions become real if/else
3. **Remove dispatcher overhead**: No more state variable checks for known paths
4. **Maintain loop structure**: The `break` statements become actual exits

**Expected deobfuscated structure**:
```c
int _hodur_func() {
    // Setup code...

    // Handler 0xB2FD8FB6 (inline)
    decrypt_algo1(enc_buf);
    printf(...);

    // Handler 0xC6685257 (inline)
    fn_WinHttpSetOption = resolve_api(...);
    fn_WinHttpSetOption(...);

    // ... more handlers inline ...

    // Handler 0x0B8148F6 with conditional
    hRequest = fn_WinHttpOpenRequest(...);
    if (!hRequest) goto error;

    // ... continue ...

error:
    printf("Error...");
    // cleanup

success:
    printf("Success...");
    // cleanup
}
```

---

## Key Insights for Implementation

1. **Hodur vs O-LLVM**: Hodur uses `if/else if` chains, not switch. Each state check is a separate conditional jump, not a jump table.

2. **Cascading unreachability risk**: If ALL predecessors of a state check are redirected, the check becomes unreachable. Must ensure at least one path remains or the check is truly dead.

3. **State variable tracking**: Must track backward accurately. If tracking hits the dispatcher loop and returns to the same state check, mark as "unknown" to avoid incorrect redirects.

4. **Conditional transitions**: Some handlers have internal conditionals that affect the next state. These must be preserved as real if/else in the deobfuscated code.

---

## Files

- Source: `samples/src/c/hodur_c2_flattened.c`
- Binary: `samples/bins/libobfuscated.dylib` (function at 0x5680)
- Unflattener: `src/d810/optimizers/microcode/flow/flattening/unflattener_hodur.py`
- Detection: `src/d810/optimizers/microcode/flow/flattening/dispatcher_detection.py`
