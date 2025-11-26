# D810-NG Tests

**Important:** Run all tests from the project root directory.

## Directory Structure

```text
tests/
├── unit/           # Fast tests, no IDA Pro required
│   ├── mba/        # MBA package tests (DSL, Z3 verification)
│   └── core/       # Core infrastructure tests
├── system/         # Slow tests, requires IDA Pro + binaries
│   └── optimizers/ # Optimizer integration tests
├── conftest.py     # Shared fixtures (env, clang, code comparison)
└── run_tests*.py   # Legacy test runners
```

## Running Tests

### Unit Tests (No IDA Required)

```bash
# Run all unit tests
pytest tests/unit/ -v

# Run MBA rule verification tests
pytest tests/unit/mba/ -v

# Run a specific test
pytest tests/unit/mba/test_verifiable_rules.py -v
```

### System Tests (Requires IDA Pro)

System tests run against IDA Pro and test actual decompilation/optimization against real obfuscated binaries.

**Option 1: Headless via pytest** (using `idapro` module / idalib)

```bash
# Run all system tests
pytest tests/system/ -v

# Run specific system test
pytest tests/system/test_libdeobfuscated.py -v
```

**Option 2: IDA GUI via testbed** (interactive)

Inside IDA Pro, run the testbed GUI:

```python
from d810.ui.testbed import show_gui
show_gui()
```

This opens an interactive test runner that auto-discovers tests in `tests/system/`.

### Docker Testing (Recommended for CI)

```bash
# Run all tests with IDA Pro 8.x
./test_with_docker.sh

# Run all tests with IDA Pro 9.2
./test_with_docker.sh idapro-tests-9.2
```

## Test Fixtures

Fixtures are defined in `conftest.py` files and auto-injected by pytest:

- **`tests/conftest.py`** - Shared fixtures: `env`, `clang_index`, `code_comparator`
- **`tests/unit/conftest.py`** - Unit test config (minimal)
- **`tests/system/conftest.py`** - IDA fixtures: `ida_database`, `d810_state`, `assert_code_*`

See the conftest files for detailed documentation on available fixtures.

## Troubleshooting

### Import Error: `ModuleNotFoundError: No module named 'd810'`

If you get import errors, set the Python path explicitly:

```bash
PYTHONPATH=src pytest tests/unit/ -v
PYTHONPATH=src pytest tests/system/ -v
```
