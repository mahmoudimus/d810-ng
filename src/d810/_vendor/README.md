# Vendored Dependencies

This directory contains vendored (bundled) dependencies for d810 to ensure consistent behavior across different IDA Pro environments and avoid dependency conflicts.

## Why Vendor Dependencies?

IDA Pro's Python environment can be challenging:
- **Version conflicts**: IDA may bundle its own versions of packages
- **Installation issues**: Users may not have write access to IDA's Python
- **Consistency**: Different IDA versions/platforms have different packages
- **Isolation**: Avoid breaking d810 when IDA updates its Python environment

By vendoring critical dependencies, we ensure d810 works reliably regardless of the IDA Pro environment.

## Architecture

This follows pip's vendoring approach:
https://github.com/pypa/pip/tree/main/src/pip/_vendor

```
d810/_vendor/
├── __init__.py          # Package marker (no import magic needed)
├── vendor.txt           # Dependency manifest
├── README.md            # This file
└── <package>/           # Vendored package source (when needed)
    └── ...
```

**Key Design Principle**: No `sys.path` manipulation or import hooks needed!
Python's standard import system handles everything naturally.

## How It Works

### Standard Python Imports
When you vendor a package like `miasm`, Python's import system naturally resolves:

```python
# This import:
from d810._vendor.miasm.arch.x86.ira import ir_a_x86_32

# Works because:
# 1. Python finds d810/_vendor/ (it's a package)
# 2. Python finds d810/_vendor/miasm/ (it's a subdirectory)
# 3. Python imports from d810/_vendor/miasm/arch/x86/ira.py
```

**No magic, just standard Python imports!**

### In d810 Code
```python
# Old (direct dependency):
from miasm.arch.x86.ira import ir_a_x86_32

# New (vendored):
from d810._vendor.miasm.arch.x86.ira import ir_a_x86_32
```

## When to Vendor a Dependency

Vendor a dependency when:
- ✅ It causes conflicts with IDA Pro's bundled packages
- ✅ We need a specific version not available in IDA
- ✅ We need to apply custom patches for IDA compatibility
- ✅ It's critical for d810's core functionality
- ✅ It's not available in PyPI or installation is problematic

**Don't vendor** when:
- ❌ Package works fine as a regular dependency
- ❌ Package is large and rarely causes issues
- ❌ We don't need a specific version

## Current Status

**Currently vendored**: None (infrastructure ready, no packages vendored yet)

**Candidates for future vendoring**:
- `miasm2`: If we need custom patches for IDA compatibility
- `z3-solver`: If bundling is needed for binary distributions

## Vendoring a New Package

### 1. Evaluate Need
Ask:
- Does this package cause conflicts in IDA Pro?
- Do we need a specific version or custom patches?
- Is the maintenance burden worth the benefit?

### 2. Download Package Source
```bash
# Clone from source
git clone https://github.com/package/repo /tmp/package
cd /tmp/package
git checkout v1.2.3  # Specific version

# Or download release
wget https://github.com/package/repo/archive/v1.2.3.tar.gz
tar xzf v1.2.3.tar.gz
```

### 3. Copy to Vendor Directory
```bash
# Copy package source (not the repo, just the package)
cp -r /tmp/package/src/package src/d810/_vendor/package

# Remove unnecessary files
rm -rf src/d810/_vendor/package/tests/
rm -rf src/d810/_vendor/package/.git/
rm -rf src/d810/_vendor/package/__pycache__/
```

### 4. Update vendor.txt
```bash
echo "package==1.2.3+d810.1" >> src/d810/_vendor/vendor.txt
echo "    # Custom patches for IDA compatibility" >> src/d810/_vendor/vendor.txt
```

### 5. Create Patches (if needed)
If the vendored package imports other packages that we also vendor, create a patch:

```bash
# Create patch file
cat > tools/vendoring/patches/package.patch << 'EOF'
diff --git a/src/d810/_vendor/package/submodule.py b/src/d810/_vendor/package/submodule.py
--- a/src/d810/_vendor/package/submodule.py
+++ b/src/d810/_vendor/package/submodule.py
@@ -1,4 +1,4 @@
-from dependency import something
+from d810._vendor.dependency import something
EOF

# Apply patch
cd src/d810/_vendor/package
patch -p4 < ../../../../tools/vendoring/patches/package.patch
```

### 6. Update Imports in d810
```bash
# Find all imports of the package
grep -r "from package import" src/d810/
grep -r "import package" src/d810/

# Replace with vendored imports
# from package → from d810._vendor.package
# import package → import d810._vendor.package as package
```

### 7. Test Thoroughly
```bash
# Run tests
pytest tests/

# Test in IDA Pro
# Load d810 in IDA and verify vendored package works
```

### 8. Document
Update this README with:
- Why the package was vendored
- What version is vendored
- Any patches applied
- Testing notes

## Using Automation Tools (Optional)

For easier vendoring, you can use the `vendoring` tool (like pip does):

```bash
# Install vendoring tool
pip install vendoring

# Configure in pyproject.toml (see Configuration section below)

# Vendor all dependencies from vendor.txt
vendoring sync .

# Update a specific package
vendoring update . package-name
```

## Configuration

### pyproject.toml
```toml
[tool.vendoring]
destination = "src/d810/_vendor/"
requirements = "src/d810/_vendor/vendor.txt"
namespace = "d810._vendor"
protected-files = ["__init__.py", "README.md", "vendor.txt"]
patches-dir = "tools/vendoring/patches"

[tool.vendoring.transformations]
drop = [
    # Exclude unnecessary files to reduce size
    "*.c",           # C extension source (we don't compile vendored packages)
    "*.so",          # Compiled extensions
    "test/",         # Tests
    "tests/",
    "example/",
    "examples/",
    "doc/",
    "docs/",
    ".git/",
    ".github/",
    "__pycache__/",
    "*.pyc",
]

substitute = [
    # Rewrite imports if vendored packages import each other
    # Example: {match='from dependency import', replace='from d810._vendor.dependency import'}
]

[tool.pytest.ini_options]
# Exclude vendored packages from testing
addopts = ["--ignore=src/d810/_vendor"]

[tool.coverage.run]
# Exclude vendored packages from coverage
omit = ["*/d810/_vendor/*"]
```

### .gitignore
```gitignore
# Vendored package caches
src/d810/_vendor/**/__pycache__/
src/d810/_vendor/**/*.pyc
src/d810/_vendor/**/*.pyo

# Don't ignore vendored source itself
# (vendored packages ARE checked into git)
```

## Maintenance

### Updating a Vendored Package

1. Update version in `vendor.txt`
2. Remove old package: `rm -rf src/d810/_vendor/package`
3. Follow "Vendoring a New Package" steps above
4. Re-apply patches from `tools/vendoring/patches/`
5. Test thoroughly
6. Commit with descriptive message

### Removing a Vendored Package

1. Remove from `src/d810/_vendor/package/`
2. Remove from `vendor.txt`
3. Remove patches from `tools/vendoring/patches/`
4. Update all imports in d810 code
5. Update this README
6. Test thoroughly

## Best Practices

1. **Version pinning**: Always pin exact versions in `vendor.txt`
2. **Minimal vendoring**: Only vendor what's absolutely necessary
3. **Document patches**: Every patch needs a comment explaining why
4. **Test in IDA**: Always test vendored packages in actual IDA Pro
5. **Track upstream**: Monitor vendored packages for security updates
6. **Clean commits**: One package per commit for easy rollback

## Troubleshooting

### Import Errors
```
ModuleNotFoundError: No module named 'd810._vendor.package'
```
**Fix**: Verify package is in `src/d810/_vendor/package/` with `__init__.py`

### Circular Imports
```
ImportError: cannot import name 'X' from partially initialized module
```
**Fix**: Check for circular imports in vendored packages. May need patching.

### Version Conflicts
```
Package 'X' requires 'Y>=2.0' but vendored version is 1.5
```
**Fix**: Update vendored package or patch to remove version check if safe.

## References

- [pip's vendoring documentation](https://github.com/pypa/pip/tree/main/src/pip/_vendor)
- [vendoring tool](https://pypi.org/project/vendoring/)
- [Why vendor dependencies?](https://pythonspeed.com/articles/vendoring/)

## Questions?

- Check pip's implementation for reference: https://github.com/pypa/pip/tree/main/src/pip/_vendor
- The key insight: **No import magic needed!** Just use standard Python imports with the `d810._vendor` namespace.
