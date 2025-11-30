#!/usr/bin/env bash
# install_triton_local.sh
# Install Triton Python bindings and dependencies locally:
# - libcapstone >=5.0.x
# - libboost    >=1.68        (system or Homebrew)
# - libz3       >=4.6.0

set -e

# Helper: print and run
run() { echo "+ $*"; "$@"; }

# Function to install triton.so to current Python environment
install_to_python() {
    local script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
    local triton_so_path
    
    # Detect Python and get version first
    local python_exe="$(which python 2>/dev/null || which python3 2>/dev/null)"
    if [[ -z "$python_exe" ]]; then
        echo "Error: Could not find Python in PATH"
        exit 1
    fi
    
    local python_abi_ver="$($python_exe -c 'import sys; print(f"{sys.version_info[0]}.{sys.version_info[1]}")')"
    
    # Try to find triton.so in the expected location (try script dir first, then current dir)
    if [[ -f "$script_dir/Triton/build/triton/lib/python${python_abi_ver}/site-packages/triton.so" ]]; then
        triton_so_path="$script_dir/Triton/build/triton/lib/python${python_abi_ver}/site-packages/triton.so"
    elif [[ -f "$script_dir/../Triton/build/triton/lib/python${python_abi_ver}/site-packages/triton.so" ]]; then
        triton_so_path="$script_dir/../Triton/build/triton/lib/python${python_abi_ver}/site-packages/triton.so"
    elif [[ -f "Triton/build/triton/lib/python${python_abi_ver}/site-packages/triton.so" ]]; then
        triton_so_path="Triton/build/triton/lib/python${python_abi_ver}/site-packages/triton.so"
    elif [[ -f "$(pwd)/Triton/build/triton/lib/python${python_abi_ver}/site-packages/triton.so" ]]; then
        triton_so_path="$(pwd)/Triton/build/triton/lib/python${python_abi_ver}/site-packages/triton.so"
    else
        echo "Error: triton.so not found for Python ${python_abi_ver}"
        echo "Searched in:"
        echo "  - $script_dir/Triton/build/triton/lib/python${python_abi_ver}/site-packages/"
        echo "  - $(pwd)/Triton/build/triton/lib/python${python_abi_ver}/site-packages/"
        echo "Build Triton first by running this script without --install-only"
        exit 1
    fi
    
    local python_site_packages="$($python_exe -c 'import site; print(site.getsitepackages()[0])')"
    
    echo "Installing triton.so to: $python_site_packages"
    cp "$triton_so_path" "$python_site_packages/"
    
    # Verify installation
    if $python_exe -c "import triton; print(f'Triton installed successfully: {triton.__file__}')" 2>/dev/null; then
        echo "Successfully installed triton to Python environment"
    else
        echo "Warning: Installation completed but import test failed"
        exit 1
    fi
}

# Parse command line arguments
INSTALL_PYTHON=false
BUILD=true

while [[ $# -gt 0 ]]; do
    case $1 in
        -i|--install-python)
            INSTALL_PYTHON=true
            shift
            ;;
        --install-only)
            INSTALL_PYTHON=true
            BUILD=false
            shift
            ;;
        -h|--help)
            echo "Usage: $0 [OPTIONS]"
            echo ""
            echo "Options:"
            echo "  -i, --install-python    Install triton.so to current Python environment"
            echo "  --install-only          Only install to Python (skip build)"
            echo "  -h, --help              Show this help message"
            echo ""
            echo "By default, builds and installs Triton to Triton/build/triton/"
            echo "Use --install-python to also install to your Python environment"
            exit 0
            ;;
        *)
            echo "Unknown option: $1"
            echo "Use -h or --help for usage information"
            exit 1
            ;;
    esac
done

# If only installing to Python, do that and exit
if [[ "$INSTALL_PYTHON" == true && "$BUILD" == false ]]; then
    install_to_python
    exit 0
fi

# 1. Install prerequisites (macOS: Homebrew)
if [[ "$(uname)" == "Darwin" ]]; then
  run brew install capstone boost z3 llvm@15
fi

# 2. Detect Python (pyenv/virtualenv-aware)
#
# If using pyenv with a virtualenv, activate it first:
#   pyenv install 3.13.5
#   pyenv virtualenv 3.13.5 triton-3.13
#   pyenv activate triton-3.13
# 
# This script autodetects the python in your current PATH,
# which will be your pyenv/virtualenv python if activated.

# Customizable Python version just for detection fallback
PYTHON_VER=3.13

# Try to find the active Python executable (prefer current)
PYTHON_EXE="$(which python 2>/dev/null || which python${PYTHON_VER} 2>/dev/null || which python3 2>/dev/null)"
if [[ -z "$PYTHON_EXE" ]]; then
  echo "Could not find Python in PATH. Activate a pyenv or virtualenv, or specify basename python."
  exit 1
fi

# Use pyenv Python framework root for library detection
PYTHON_ROOT="/Users/mahmoud/.pyenv/versions/3.13.5/Library/Frameworks/Python.framework/Versions/3.13"
PYTHON_PREFIX="$PYTHON_ROOT"
PYTHON_INCLUDE="$PYTHON_ROOT/include/python3.13"

# Find the Python library in the framework root
PYTHON_ABI_VER="$($PYTHON_EXE -c 'import sys; print(f"{sys.version_info[0]}.{sys.version_info[1]}")')"
PYTHON_LIB="$(find "$PYTHON_ROOT" \( -name "libpython${PYTHON_ABI_VER}*.dylib" -o -name "libpython${PYTHON_ABI_VER}*.so" \) | head -n1)"

if [[ ! -f "$PYTHON_LIB" ]]; then
  echo "Python library not found in \$PYTHON_ROOT ($PYTHON_ROOT)."
  echo "Searched for: libpython${PYTHON_ABI_VER}*.dylib or libpython${PYTHON_ABI_VER}*.so"
  exit 1
fi

# 3. Clone Triton if not present
if [[ ! -d Triton ]]; then
  run git clone https://github.com/JonathanSalwan/Triton
fi

cd Triton
mkdir -p build && cd build

# 4. Configure build for local Python and dependencies
LLVM_PREFIX=$(brew --prefix llvm@15 2>/dev/null || true)
CAPSTONE_PREFIX=$(brew --prefix capstone 2>/dev/null || true)
Z3_PREFIX=$(brew --prefix z3 2>/dev/null || true)
BOOST_PREFIX=$(brew --prefix boost 2>/dev/null || true)

CMAKE_PREFIX_PATH="$LLVM_PREFIX;$CAPSTONE_PREFIX;$Z3_PREFIX;$BOOST_PREFIX"

# Install to triton subdirectory in the build directory
TRITON_INSTALL_PREFIX="$(pwd)/triton"

run cmake .. \
  -DCMAKE_INSTALL_PREFIX="$TRITON_INSTALL_PREFIX" \
  -DPYTHON_EXECUTABLE="$PYTHON_EXE" \
  -DPYTHON_LIBRARIES="$PYTHON_LIB" \
  -DPYTHON_INCLUDE_DIRS="$PYTHON_INCLUDE" \
  -DCAPSTONE_ROOT="$CAPSTONE_PREFIX" \
  -DZ3_ROOT="$Z3_PREFIX" \
  -DLLVM_INTERFACE=ON \
  -DCMAKE_PREFIX_PATH="$CMAKE_PREFIX_PATH"

run make -j$(nproc)
run make install

echo "Triton installed to $TRITON_INSTALL_PREFIX"
echo "Add to PYTHONPATH: export PYTHONPATH=\"$TRITON_INSTALL_PREFIX/lib/python${PYTHON_ABI_VER}/site-packages:\$PYTHONPATH\""

# Install to Python environment if requested
if [[ "$INSTALL_PYTHON" == true ]]; then
    echo ""
    echo "Installing to Python environment..."
    cd "$(dirname "$0")" || cd "$(dirname "${BASH_SOURCE[0]}")" || true
    install_to_python
fi