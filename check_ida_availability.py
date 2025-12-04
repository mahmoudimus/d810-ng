#!/usr/bin/env python3
"""Check IDA Pro availability and environment."""
import sys
import subprocess

print("=" * 60)
print("1. Checking idapro module...")
try:
    import idapro
    print("   ✓ idapro module is available")
except ImportError as e:
    print(f"   ✗ idapro module NOT available: {e}")
    sys.exit(1)

print("\n2. Checking ida64 binary...")
result = subprocess.run(["which", "ida64"], capture_output=True, text=True)
if result.returncode == 0:
    print(f"   ✓ ida64 found at: {result.stdout.strip()}")
else:
    print("   ✗ ida64 not in PATH")
    # Try /Applications
    result = subprocess.run(["find", "/Applications", "-name", "ida64", "-type", "f"],
                          capture_output=True, text=True, timeout=5)
    if result.stdout.strip():
        print(f"   Found in /Applications: {result.stdout.strip()}")
    else:
        print("   Not found in /Applications either")

print("\n3. Python version and path:")
print(f"   {sys.version}")
print(f"   {sys.executable}")

print("\n4. Attempting to run a simple test...")
result = subprocess.run(
    [sys.executable, "-m", "pytest",
     "tests/system/test_libdeobfuscated_dsl.py::TestDeobfuscationDSL::test_abc_patterns",
     "-v", "-s"],
    cwd="/Users/mahmoud/src/idapro/d810-ng",
    capture_output=True,
    text=True,
    timeout=120
)

print(f"   Exit code: {result.returncode}")
if result.stdout:
    print("\n   STDOUT (last 50 lines):")
    lines = result.stdout.split('\n')
    for line in lines[-50:]:
        print(f"   {line}")

if result.stderr:
    print("\n   STDERR (last 30 lines):")
    lines = result.stderr.split('\n')
    for line in lines[-30:]:
        print(f"   {line}")

print("\n" + "=" * 60)
print(f"Result: {'PASS' if result.returncode == 0 else 'FAIL'}")
