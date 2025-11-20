---
description: Direct IDA Pro 9.2 installation in sandboxed environments without Docker. Alternative method when Docker image pull fails due to VFS storage limitations.
tags: [ida-pro, installation, testing, sandboxed, alternative-to-docker]
---

# Direct IDA Pro Installation Skill

This skill provides an alternative method for installing IDA Pro 9.2 directly from a zip archive when Docker-based installation fails due to storage limitations in sandboxed environments.

## When to Use This Method

Use this method when:
- Docker image pull fails with "no space left on device" despite available disk space
- VFS storage driver cannot handle large (2-4GB) image extraction
- You need a faster setup without Docker overhead
- You have access to an IDA Pro installation archive

## Prerequisites

- Root access (or sufficient permissions)
- Internet connectivity (for downloading dependencies)
- IDA Pro installation archive (zip/tar.gz format)
- Archive password (if encrypted)

## Installation Steps

### 1. Obtain IDA Pro Archive

User should provide:
- Download URL for IDA Pro archive
- Password for encrypted archive (if applicable)
- Expected archive format (zip, tar.gz, tar.xz, etc.)

Example:
```bash
# Download from provided URL
curl -L -o /tmp/ida92.zip "https://example.com/ida92.zip"

# Or use wget
wget -O /tmp/ida92.zip "https://example.com/ida92.zip"
```

### 2. Extract Archive

For password-protected zip files:
```bash
# Extract with password
unzip -P "password" -qq /tmp/ida92.zip

# Extract nested tar archives if present
xz -d ida92.tar.xz
tar xf ida92.tar
```

For standard archives:
```bash
# Zip
unzip -qq /tmp/ida92.zip

# Tar.gz
tar xzf /tmp/ida92.tar.gz

# Tar.xz
tar xJf /tmp/ida92.tar.xz
```

### 3. Run Setup Script

The archive typically includes a `setup_ida.sh` script that handles:
- Python environment setup via `uv`
- IDA Pro installer execution
- License generation (if keygen/reggen scripts included)
- Python package installation
- IDA Python integration (idapyswitch)

```bash
cd /tmp  # or wherever you extracted
chmod +x setup_ida.sh
./setup_ida.sh
```

### 4. Verify Installation

After successful installation:
```bash
# Check IDA installation
ls -la /app/ida/

# Check Python environment
/app/ida/.venv/bin/python3 --version

# Check IDA Python package
/app/ida/.venv/bin/python3 -c "import idaapi; print('IDA API available')"

# Verify license
ls -la /root/.idapro/idapro.hexlic
```

Expected structure:
```
/app/ida/              # IDA Pro installation directory
/app/ida/.venv/        # Python virtual environment
/root/.idapro/         # IDA user directory
/root/.idapro/idapro.hexlic  # License file
```

## Installing d810-ng Plugin

### 1. Install in Editable Mode

```bash
cd /home/user/d810-ng

# Install with dev dependencies
/app/ida/.venv/bin/python3 -m pip install -e .[dev]
```

### 2. Verify Installation

```bash
# Check d810 package is importable
/app/ida/.venv/bin/python3 -c "import d810; print(d810.__file__)"

# List installed packages
/app/ida/.venv/bin/pip list | grep d810
```

## Running Tests

### Local Tests (No IDA Required)

```bash
cd /home/user/d810-ng
/app/ida/.venv/bin/python3 tests/run_tests_local.py
```

### Integration Tests (IDA Required)

```bash
cd /home/user/d810-ng

# Run all integration tests
/app/ida/.venv/bin/python3 -m pytest tests/system -v --tb=short

# Run specific test
/app/ida/.venv/bin/python3 -m pytest tests/system/test_rule_tracking.py::TestRuleFiring::test_verify_refactored_modules_loaded -v

# Run with coverage
/app/ida/.venv/bin/python3 -m pytest tests/system -v --cov=src/d810 --cov-report=html --cov-report=xml
```

### Expected Test Results

After GUI import fix (commit 209b38d):
- ✅ `test_verify_refactored_modules_loaded` - PASSED (verifies DSL rules are registered)
- ❌ 4 tests requiring binary samples - FAILED (expected without test binaries)

## What setup_ida.sh Does

The automated setup script typically performs:

1. **Install Python via uv**:
   ```bash
   uv python install 3.10
   ```

2. **Discover libpython path**:
   ```python
   python3 -c "import sysconfig; print(sysconfig.get_config_var('LIBDIR'))"
   ```

3. **Run IDA installer in unattended mode**:
   ```bash
   ./ida9.2.run --mode unattended --installpassword "" --prefix /app/ida
   ```

4. **Generate license** (if keygen/reggen available):
   ```bash
   ./keygen.sh
   ./reggen.sh
   ```

5. **Create Python virtual environment**:
   ```bash
   python3 -m venv /app/ida/.venv
   /app/ida/.venv/bin/pip install --upgrade pip
   ```

6. **Install IDA Python package**:
   ```bash
   /app/ida/.venv/bin/pip install /app/ida/idalib/python
   ```

7. **Configure IDA Python integration**:
   ```bash
   /app/ida/.venv/bin/idapyswitch --force --auto-file /path/to/libpython3.10.so
   ```

8. **Copy license to user directory**:
   ```bash
   cp idapro.hexlic /root/.idapro/
   ```

## Troubleshooting

### setup_ida.sh not found

**Problem**: Archive doesn't include setup script

**Solution**: Manually perform installation steps:
1. Run IDA installer: `./ida*.run --mode unattended --prefix /app/ida`
2. Create venv: `python3 -m venv /app/ida/.venv`
3. Install IDA package: `/app/ida/.venv/bin/pip install /app/ida/idalib/python`
4. Run idapyswitch with libpython path

### License errors

**Problem**: IDA complains about missing or invalid license

**Solution**:
1. Check license file exists: `ls -la /root/.idapro/idapro.hexlic`
2. Verify file is not empty: `cat /root/.idapro/idapro.hexlic`
3. If using keygen/reggen, ensure they ran successfully
4. Check IDA installer logs for license generation errors

### Python import errors

**Problem**: `ModuleNotFoundError: No module named 'ida_hexrays'` or `No module named 'idaapi'`

**Root Cause**: Trying to import IDA modules without importing `idapro` first in standalone scripts.

**Solution**:

**CRITICAL: When using idalib from standalone Python scripts, you MUST:**
```python
import idapro  # ← MUST be the FIRST import before ANY IDA modules!
import idaapi  # ← Now this works
```

**Common mistakes:**
```python
# ❌ WRONG - Will fail with ModuleNotFoundError
import sys
sys.path.insert(0, '/home/user/d810-ng/src')
from d810.optimizers.dsl import *  # This imports ida_hexrays internally - FAILS!

# ✅ CORRECT - Import idapro first
import idapro  # ← CRITICAL: First import!
import sys
sys.path.insert(0, '/home/user/d810-ng/src')
from d810.optimizers.dsl import *  # Now this works
```

**Two execution contexts:**
1. **Inside IDA Pro** (GUI/headless): `import idaapi` works directly
2. **Standalone Python with idalib**: `import idapro` MUST come first

**Verification steps if still failing:**
1. Verify IDA Python package installed: `/app/ida/.venv/bin/pip list | grep idapro`
2. Check idapyswitch ran successfully: Look for "IDA installation directory set to: /app/ida" in setup output
3. Manually run idapyswitch if needed:
   ```bash
   /app/ida/.venv/bin/idapyswitch --auto-file $(python3 -c "import sysconfig; print(sysconfig.get_path('stdlib') + '/../libpython3.10.so')")
   ```
4. Verify idapro imports:
   ```bash
   /app/ida/.venv/bin/python3 -c "import idapro; import idaapi; print('OK')"
   ```

**See**: https://docs.hex-rays.com/user-guide/idalib#using-the-ida-library-python-module

### Tests fail with Qt/GUI import errors

**Problem**: `ImportError: PySide6 can only be used from the GUI version of IDA`

**Solution**: This is the same issue as Docker method. Make GUI imports conditional in plugin code:
```python
# In src/d810/manager.py (or similar)
try:
    from d810.ui.ida_ui import D810GUI
except (ImportError, NotImplementedError):
    D810GUI = None  # type: ignore

# Later:
if gui and self._is_loaded and D810GUI is not None:
    self.gui = D810GUI(self)
```

See commit 209b38d for complete fix.

### Permission errors during installation

**Problem**: Permission denied when creating directories or copying files

**Solution**:
1. Run setup script with sudo: `sudo ./setup_ida.sh`
2. Or manually create required directories:
   ```bash
   sudo mkdir -p /app/ida /root/.idapro
   sudo chown $USER:$USER /app/ida /root/.idapro
   ```

## Comparison with Docker Method

| Aspect | Direct Install | Docker |
|--------|---------------|---------|
| Setup time | ~5-10 minutes | ~15-30 minutes (if image pulls successfully) |
| Disk space | ~2-3GB | ~4-6GB (image + VFS overhead) |
| VFS issues | None | May fail with large images |
| Portability | Tied to host system | More portable |
| Cleanup | Manual removal | `docker system prune` |
| CI/CD | Requires setup in each job | Image can be cached |

**Recommendation**:
- Use Docker method for CI/CD pipelines (if VFS works)
- Use direct install for local development and troubleshooting
- Use direct install as fallback when Docker image pull fails

## Environment Configuration

After installation, tests expect:

### Python Path
```bash
PYTHONPATH=/home/user/d810-ng:/app/ida/python
```

### IDA User Directory
```bash
IDAUSR=/root/.idapro
```

### Python Executable
```bash
/app/ida/.venv/bin/python3
```

## Testing the Installation

**⚠️ CRITICAL: Understanding `import idapro` vs `import idaapi`**

When using IDA library (idalib) from standalone Python scripts:
- ✅ **MUST** import `idapro` FIRST before any IDA modules
- ✅ After `import idapro`, you can use `idaapi` and other `ida_*` modules
- ❌ **NEVER** import `idaapi` or `ida_*` modules before `import idapro`

See: https://docs.hex-rays.com/user-guide/idalib#using-the-ida-library-python-module

**Two modes of IDA Python usage:**

1. **Inside IDA Pro** (GUI or headless idat64):
   ```python
   # Direct import works - IDA is already running
   import idaapi
   import ida_funcs
   ```

2. **Standalone Python script** (using idalib):
   ```python
   # MUST import idapro FIRST
   import idapro  # ← CRITICAL: First import!

   # Now you can import IDA APIs
   import idaapi
   import ida_funcs
   ```

**Quick verification test:**
```bash
cd /home/user/d810-ng

# Test Python can import IDA modules (CORRECT WAY with idapro)
/app/ida/.venv/bin/python3 -c "
import idapro  # ← CRITICAL: Import idapro FIRST!
import idaapi
print(f'IDA Version: {idaapi.IDA_SDK_VERSION}')
"

# Test d810 imports work
# Note: d810 modules import idaapi, so this will fail unless run inside IDA
# For standalone scripts, you must ensure idapro is imported first
/app/ida/.venv/bin/python3 -c "
import idapro  # ← CRITICAL: Import idapro FIRST!
from d810.manager import D810Manager
from d810.optimizers.rules import VerifiableRule
print('d810 imports successful')
"

# Run critical integration test (pytest handles idapro import internally)
/app/ida/.venv/bin/python3 -m pytest tests/system/test_rule_tracking.py::TestRuleFiring::test_verify_refactored_modules_loaded -v
```

Expected output:
```
IDA Version: 920
d810 imports successful
test_verify_refactored_modules_loaded PASSED
```

**Why this matters:**
- Tests using `IDAProTestCase` automatically handle `idapro` import
- Standalone scripts MUST manually import `idapro` first
- Forgetting this causes: `ModuleNotFoundError: No module named 'ida_hexrays'`

## Files and Directories

Key files created by this installation method:

```
/app/ida/
├── ida64              # IDA Pro 64-bit binary
├── idat64             # IDA Pro 64-bit text-mode binary
├── python/            # IDA Python modules
│   ├── idaapi.so
│   └── ...
├── .venv/             # Python virtual environment
│   ├── bin/
│   │   ├── python3
│   │   ├── pip
│   │   └── idapyswitch
│   └── lib/
└── idalib/

/root/.idapro/
├── idapro.hexlic      # License file
├── ida-config.json    # IDA configuration
└── plugins/           # Plugin directory (for d810-ng)
```

## Related Files

- `.github/workflows/test-ida.yml` - CI workflow (uses Docker by default)
- `tests/system/` - Integration tests requiring IDA Pro
- `tests/run_tests_local.py` - Local tests not requiring IDA Pro
- `src/d810/manager.py` - Main plugin manager (needs GUI import fix)

## Notes for Future Sessions

1. **Archive source matters** - Ensure the IDA archive includes keygen/reggen scripts if license generation is needed
2. **Python version compatibility** - IDA 9.2 works with Python 3.10; verify compatibility for other IDA versions
3. **Setup script variations** - Different IDA archives may have different setup script names or structures
4. **License file location** - Always copy license to `/root/.idapro/idapro.hexlic` for tests to work
5. **Virtual environment** - Always use IDA's venv for running tests to ensure correct Python environment
6. **GUI import fix required** - Remember to apply GUI import fix (commit 209b38d) for headless testing
7. **Test binaries needed** - 4 integration tests require binary samples in `samples/bins/` to pass

## Success Criteria

Installation is successful when:
1. ✅ IDA binaries are executable: `/app/ida/idat64 -v`
2. ✅ Python can import IDA modules: `import idaapi`
3. ✅ License file exists and is valid
4. ✅ d810-ng package is installed in editable mode
5. ✅ Critical test passes: `test_verify_refactored_modules_loaded PASSED`
