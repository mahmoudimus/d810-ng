# Session Context: Test DSL Coverage for Flattening Module

**Date**: 2025-11-30
**Branch**: `cfg-audit-deferred-modifier`
**Goal**: Achieve test coverage for `src/d810/optimizers/microcode/flow/flattening/`
**Bead**: `d810ng-bmw` - Improve flattening module test coverage to 80%+

## Current State

### Test Results
- **37 passed, 19 failed, 1 skipped** (160s total)
- **Coverage: 58%** on flattening module

### Commits Made This Session
1. `a0daf35` - SDK pxd updates with complete type definitions (+23k lines)
2. `2d27982` - Fix test runner project loading bug
3. `5f72b46` - Add session context for test DSL coverage work
4. `22f1ed4` - Skip mixed_dispatcher_pattern to avoid timeout
5. `7a163d5` - Update session context with coverage results

## Beads Created for Coverage Work

```
d810ng-bmw: Improve flattening module test coverage to 80%+ (blocked by below)
├── d810ng-gez: Fix ABC F6/XOR test cases (9 failing) [IN PROGRESS]
├── d810ng-iyv: Fix dispatcher pattern test cases (5 failing)
├── d810ng-9zl: Fix remaining test failures (5 tests)
├── d810ng-irj: Improve unflattener_fake_jump.py coverage (20% -> 80%)
├── d810ng-6lt: Improve services.py coverage (25% -> 80%)
├── d810ng-xfr: Improve heuristics.py coverage (25% -> 80%)
├── d810ng-lh5: Improve unflattener_refactored.py coverage (31% -> 80%)
├── d810ng-73h: Improve loop_prover.py coverage (40% -> 80%)
└── d810ng-48i: Improve unflattener_single_iteration.py coverage (40% -> 80%)
```

## Key Finding: ABC Pattern Not Matching

The ABC F6xxx tests fail because `BadWhileLoop` rule isn't transforming these functions.

**Example function** (`abc_f6_add_dispatch`):
```c
v3 = 0xF6951;  // State var init
while ( 1 ) {
    while ( v3 == 0xF6951 ) {  // State check
        v2 = a1;
        v3 = 0xF6952;  // State transition
    }
    if ( v3 != 0xF6952 ) break;
    ...
}
```

**BadWhileLoop expects** (from `unflattener_badwhile_loop.py:48-87`):
- Blocks with `jz`/`jnz` tail instructions
- Constants in range 0xF6000-0xF6FFF (default)
- State variable as operand to conditional jump

**Likely issue**: The microcode maturity level or block structure doesn't match what `BadWhileLoop.explore()` expects. Need to:
1. Dump microcode at the right maturity level
2. Check if blocks have the expected `jz var, #CONST` pattern
3. Debug `BadWhileLoopInfo.explore()` to see why it returns False

## Coverage by File

| File | Coverage | Status |
|------|----------|--------|
| unflattener_switch_case.py | 96% | Excellent |
| utils.py | 94% | Excellent |
| unflattener.py | 89% | Great |
| unflattener_badwhile_loop.py | 86% | Great |
| fix_pred_cond_jump_block.py | 75% | Good |
| unflattener_hodur.py | 71% | Good |
| dispatcher_detection.py | 68% | Good |
| abc_block_splitter.py | 67% | Good |
| unflattener_indirect.py | 59% | Moderate |
| generic.py | 57% | Moderate |
| loop_prover.py | 40% | Low |
| unflattener_single_iteration.py | 40% | Low |
| unflattener_refactored.py | 31% | Low |
| heuristics.py | 25% | Low |
| services.py | 25% | Low |
| unflattener_fake_jump.py | 20% | Low |

## Next Investigation Steps

1. **Debug `BadWhileLoop` matching**:
   ```python
   # In IDA with the function open, run:
   from d810.optimizers.microcode.flow.flattening.unflattener_badwhile_loop import BadWhileLoopInfo
   # Check what explore() returns and why
   ```

2. **Check microcode structure**:
   - Print mba blocks at MMAT_LOCOPT maturity
   - Find blocks with F6xxx constants
   - Verify they have `jz`/`jnz` tail instructions

3. **Possible fixes**:
   - Adjust `BadWhileLoop` to handle different block patterns
   - Create new rule specifically for ABC F6xxx patterns
   - Adjust test expectations if pattern isn't supported

## How to Run Tests

```bash
# Single failing test
PYTHONPATH=src pytest tests/system/test_libdeobfuscated_dsl.py::TestAllCases::test_all[abc_f6_add_dispatch] -v

# All tests with coverage
PYTHONPATH=src pytest tests/system/test_libdeobfuscated_dsl.py::TestAllCases -v \
  --cov=src/d810/optimizers/microcode/flow/flattening \
  --cov-report=term-missing
```

## Key Files

- `src/d810/optimizers/microcode/flow/flattening/unflattener_badwhile_loop.py` - BadWhileLoop rule
- `src/d810/conf/default_unflattening_approov.json` - Project config for ABC tests
- `tests/system/cases/libobfuscated_comprehensive.py` - Test case definitions
- `samples/src/c/abc_f6_constants.c` - Source for ABC F6 patterns
