# Building D810-NG with Cython Extensions

This document explains how to build D810-NG with its Cython performance optimizations.

## Overview

D810-NG uses Cython to accelerate performance-critical code paths while maintaining a pure Python fallback for compatibility. The build system is designed to work both with and without the IDA SDK.

## Build Configuration

### Requirements

- **Python**: 3.10 or higher
- **Cython**: 3.0.0 or higher
- **setuptools**: 77.0.1 or higher
- **IDA SDK** (optional): For full Hex-Rays integration

### Build Modes

#### 1. Pure Python (No Build Required)

The plugin works out-of-the-box without building Cython extensions:

```bash
pip install -e .
```

The `CythonMode` class automatically detects if Cython extensions are available and falls back to pure Python implementations in `_slow_ast.py`.

#### 2. Cython Extensions (Performance Build)

To build with Cython optimizations:

```bash
pip install -e .[speedups]
```

Or explicitly:

```bash
pip install Cython>=3.0.0
python setup.py build_ext --inplace
```

#### 3. Debug Build

For development with debug symbols and profiling:

```bash
DEBUG=1 python setup.py build_ext --inplace
```

This enables:
- Debug symbols (`-g`, `-ggdb`)
- Line tracing for profiling
- Coverage support
- Assertions enabled

## GitHub Actions Workflow

### Automated Wheel Building

The `.github/workflows/build-cython.yml` workflow automatically builds platform-specific wheels:

**Triggered on:**
- Push to `main` or `faster` branches
- Version tags (`v*`)
- Pull requests
- Manual workflow dispatch

**Builds for:**
- **Linux**: x86_64 (Ubuntu latest)
- **macOS**: x86_64 (macos-13) and ARM64 (macos-latest)
- **Windows**: x86_64 (Windows latest)

**Python versions:** 3.10, 3.11, 3.12, 3.13

### Workflow Jobs

1. **build_wheels**
   - Uses `cibuildwheel` to build platform-specific wheels
   - Runs basic import tests
   - Uploads wheel artifacts

2. **build_sdist**
   - Creates source distribution
   - Includes Cython `.pyx` files for rebuilding
   - Validates with `twine check`

3. **test_import**
   - Downloads and installs built wheels
   - Tests basic imports
   - Verifies Cython mode detection

4. **upload_artifacts** (tags only)
   - Uploads wheels to GitHub releases
   - Triggered only on version tags

## Package Distribution

### What's Included

The distribution includes:

- **Source files**: `.pyx`, `.pxd` files for Cython
- **Headers**: `.h`, `.hpp` files from `include/`
- **Cythonized C**: `.c`, `.cpp` intermediate files (sdist only)
- **Pure Python fallback**: `_slow_ast.py`

### Installation Options

```bash
# Install from PyPI (when published)
pip install d810

# Install with Cython speedups
pip install d810[speedups]

# Development install
pip install -e .[dev]

# CI install
pip install -e .[ci]
```

## Local Development

### Initial Setup

```bash
# Clone repository
git clone https://github.com/yourusername/d810-ng.git
cd d810-ng

# Create virtual environment
python3.10 -m venv venv
source venv/bin/activate  # or `venv\Scripts\activate` on Windows

# Install in development mode with all dependencies
pip install -e .[dev]

# Build Cython extensions
python setup.py build_ext --inplace
```

### Rebuilding After Changes

After modifying `.pyx` files:

```bash
# Clean previous builds
rm -rf build/ *.so *.pyd

# Rebuild
python setup.py build_ext --inplace
```

### Testing Cython Mode

```python
from d810.cythxr.cymode import CythonMode

mode = CythonMode()
print(f"Cython enabled: {mode.is_enabled()}")
```

## Architecture

### Module Structure

```
src/d810/
├── expr/
│   ├── ast.py              # Dispatcher (Cython or Python)
│   ├── _ast.pyx            # Cython implementation
│   ├── _slow_ast.py        # Pure Python fallback
│   ├── ast.pxd             # Cython header
│   └── _ast_evaluate.pyx   # Fast AST evaluator
├── cythxr/
│   ├── cymode.py           # Runtime Cython detection
│   ├── _chexrays.pxd       # Hex-Rays API declarations
│   └── _chexrays_api.pyx   # Hex-Rays Cython wrappers
└── optimizers/
    └── microcode/
        └── flow/
            └── constant_prop/
                ├── _fast_dataflow.pyx
                └── _stackvars_constprop.pyx
```

### Import Flow

1. `ast.py` checks `CythonMode().is_enabled()`
2. If Cython available: imports from `_ast.pyx`
3. If not available: imports from `_slow_ast.py`
4. No code changes needed - transparent fallback

## Platform-Specific Notes

### macOS

- Requires macOS 10.9+ (set in `setup.py`)
- ARM64 builds on macos-latest runners
- x86_64 builds on macos-13 runners
- Uses `@loader_path` for rpath

### Linux

- Builds with GCC
- Uses `$ORIGIN` for rpath
- Suppresses IDA SDK-specific warnings

### Windows

- Builds with MSVC
- Uses `/TP` for C++ mode
- Uses `/EHa` for exception handling

## Troubleshooting

### Cython Not Found

```bash
pip install "Cython>=3.0.0"
```

### Build Failures

```bash
# Clean everything
rm -rf build/ dist/ *.egg-info/ **/*.so **/*.pyd

# Rebuild
pip install -e . --no-cache-dir --force-reinstall
```

### Import Errors

Check if Cython modules are loaded:

```python
import sys
print([m for m in sys.modules if 'd810' in m])
```

## References

- **Cython Documentation**: https://cython.readthedocs.io/
- **cibuildwheel**: https://cibuildwheel.readthedocs.io/
- **ida-sigmaker**: https://github.com/mahmoudimus/ida-sigmaker (reference implementation)
