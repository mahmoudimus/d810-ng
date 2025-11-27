# ==============================================================================
# Universal Clang-First Cross-Platform Makefile (Linux ↔ Windows ↔ macOS) – 2025
#
# Features
# • Always uses Clang / clang-cl / Apple clang
# • Cross-compiles perfect Windows DLLs from Linux or macOS (lld + MinGW target)
# • Builds pure x86_64 macOS dylibs even on Apple Silicon
# • Ignores undefined symbols the correct way on every platform
# • Extremely forgiving architecture selection (see examples below)
# • Full debug info, zero optimizations, no inlining/vectorization
# • Single Makefile – works everywhere, no conditionals needed per host
#
# Usage examples (from the samples directory)
#   make                                 # → Windows x86_64 DLL (default)
#   make TARGET_OS=linux                 # → Linux .so for host arch
#   make TARGET_OS=darwin BUILD_ARCH=x86_64   # → pure Intel macOS dylib
#   make TARGET_OS=darwin BUILD_ARCH=arm64    # → Apple Silicon dylib
#   make BUILD_ARCH=x86                  # → 32-bit Windows DLL
#   make BINARY_NAME=myplugin            # → bins/myplugin.dll (no host/arch suffix)
#   make clean
# ==============================================================================

# ----------------------------- Host detection -----------------------------
ifeq ($(OS),Windows_NT)
    UNAME_S :=
    HOST_OS := windows
    RM      := del /Q 2>nul || ver>nul
    MKDIR   := mkdir
else
    UNAME_S := $(shell uname -s)
    ifeq ($(UNAME_S),Darwin)
        HOST_OS := darwin
    else
        HOST_OS := linux
    endif
    RM      := rm -f
    MKDIR   := mkdir -p
endif

# ----------------------------- User configurable options -----------------------------
# windows | darwin | linux | native
TARGET_OS    ?= windows
# x86_64 | x86 | arm64 | aarch64 | -m32 | -arch arm64 | etc.
BUILD_ARCH   ?= x86_64
# libobfuscated by default
BINARY_NAME  ?= libobfuscated

# ----------------------------- Normalize native -----------------------------
ifeq ($(TARGET_OS),native)
    TARGET_OS := $(HOST_OS)
endif

# ----------------------------- Super-friendly architecture handling -----------------------------
RAW_ARCH := $(or $(BUILD_ARCH),x86_64)

# Normalized name for filename (bins/libobfuscated_linux_x86_64.dll)
NORM_ARCH := $(strip \
    $(if $(findstring 64,$(RAW_ARCH)),x86_64,\
    $(if $(findstring arm64,$(RAW_ARCH)),arm64,\
    $(if $(findstring aarch64,$(RAW_ARCH)),arm64,\
    $(if $(findstring 32,$(RAW_ARCH)),x86,\
    $(if $(findstring x86,$(RAW_ARCH)),x86,x86_64))))))

# Convert to real compiler flags Clang understands, per target OS
# If the user gave explicit flags (e.g. "-m32" or "-arch arm64"), trust them.
ARCH_FLAGS :=
ifneq ($(filter -%,$(RAW_ARCH)),)
    ARCH_FLAGS := $(RAW_ARCH)
else
    # Plain architecture name → choose flags based on TARGET_OS
    ifeq ($(TARGET_OS),darwin)
        NORM_FLAG_x86_64 := -arch x86_64
        NORM_FLAG_x86    := -arch i386
        NORM_FLAG_arm64  := -arch arm64
        ARCH_FLAGS := $(NORM_FLAG_$(NORM_ARCH))
    else ifeq ($(TARGET_OS),linux)
        NORM_FLAG_x86_64 := -m64
        NORM_FLAG_x86    := -m32
        ARCH_FLAGS := $(NORM_FLAG_$(NORM_ARCH))
    else ifeq ($(TARGET_OS),windows)
        # For MinGW cross, the architecture is encoded in the triple
        # (i686-w64-mingw32 vs x86_64-w64-mingw32), so we leave ARCH_FLAGS empty.
        ARCH_FLAGS :=
    endif
endif

# Prevent Make's built-in rules from injecting garbage
override TARGET_ARCH :=

# ----------------------------- Toolchain selection (Clang everywhere) -----------------------------
CC_BASE := clang

# On Windows host → prefer clang-cl.exe (MSVC-compatible) if it exists
ifeq ($(HOST_OS),windows)
    ifneq ($(shell where clang-cl.exe 2>nul),)
        CC_BASE     := clang-cl.exe
        USING_CLANG_CL := 1
    endif
endif

# Target-specific compiler/linker selection
ifeq ($(TARGET_OS),windows)
    ifneq ($(USING_CLANG_CL),1)
        # Cross-compiling to Windows → MinGW target + lld
        ifeq ($(NORM_ARCH),x86)
            TRIPLE := i686-w64-mingw32
        else
            TRIPLE := x86_64-w64-mingw32
        endif
        CC  := $(CC_BASE) --target=$(TRIPLE) -fuse-ld=lld
        LD  := $(CC_BASE) --target=$(TRIPLE) -fuse-ld=lld
    else
        CC  := $(CC_BASE)
        LD  := $(CC_BASE)
    endif
    OUTPUT_EXT := dll
    # Optional: point to a MinGW / llvm-mingw sysroot when cross-compiling
    # Example: make TARGET_OS=windows MINGW_SYSROOT=/opt/llvm-mingw
    MINGW_SYSROOT ?=
    ifneq ($(MINGW_SYSROOT),)
        CC := $(CC) --sysroot=$(MINGW_SYSROOT)
        LD := $(LD) --sysroot=$(MINGW_SYSROOT)
        MINGW_INCLUDEDIR ?= $(MINGW_SYSROOT)/include
        MINGW_LIBDIR     ?= $(MINGW_SYSROOT)/lib
    endif
else ifeq ($(TARGET_OS),darwin)
    CC  := $(CC_BASE)
    LD  := $(CC_BASE)
    OUTPUT_EXT := dylib
else
    CC  := $(CC_BASE)
    LD  := $(CC_BASE)
    OUTPUT_EXT := so
endif

# Apply architecture flags
CC := $(CC) $(ARCH_FLAGS)
LD := $(LD) $(ARCH_FLAGS)

# ----------------------------- Output naming -----------------------------
ifneq ($(origin BINARY_NAME),default)
    TARGET_LIB := bins/$(BINARY_NAME).$(OUTPUT_EXT)
else
    TARGET_LIB := bins/$(BINARY_NAME)_$(HOST_OS)_$(NORM_ARCH).$(OUTPUT_EXT)
endif

# ----------------------------- Compiler & Linker flags (your exact debug setup) -----------------------------
CFLAGS_BASE := -Wall -Wextra \
               -O0 -g -Iinclude \
               -fno-inline -fno-builtin \
               -fno-vectorize -fno-slp-vectorize \
               -fno-omit-frame-pointer

ifeq ($(TARGET_OS),windows)
    ifeq ($(USING_CLANG_CL),1)
        # Native Windows with clang-cl (MSVC mode)
        CFLAGS  := $(CFLAGS_BASE) /MDd
        LDFLAGS := /DLL /DEBUG:FULL /FORCE:UNRESOLVED
    else
        # Cross-compile with Clang → MinGW
        CFLAGS  := $(CFLAGS_BASE)
        ifneq ($(MINGW_INCLUDEDIR),)
            CFLAGS  += -I$(MINGW_INCLUDEDIR)
        endif
        LDFLAGS := -shared -fuse-ld=lld \
                   -Wl,--export-all-symbols \
                   -Wl,--enable-auto-import \
                   -Wl,--unresolved-symbols=ignore-all
        ifneq ($(MINGW_LIBDIR),)
            LDFLAGS += -L$(MINGW_LIBDIR)
        endif
    endif
else
    # Linux / macOS
    CFLAGS  := $(CFLAGS_BASE) -fPIC $(ARCH_FLAGS)

    ifeq ($(TARGET_OS),darwin)
        LDFLAGS := -shared -undefined dynamic_lookup $(ARCH_FLAGS)
    else
        LDFLAGS := -shared -Wl,--unresolved-symbols=ignore-in-shared-libs $(ARCH_FLAGS)
    endif
endif

# Keep debug symbols in the final binary everywhere
LDFLAGS += -g

# ----------------------------- Sources & Objects -----------------------------
SRCS := $(wildcard src/c/*.c)
OBJS := $(SRCS:.c=.o)

# ----------------------------- Rules -----------------------------
.PHONY: all clean

all: bins $(TARGET_LIB)

bins:
	@$(MKDIR) bins >nul 2>&1 || $(MKDIR) bins

# Build target - different for MSVC vs GCC/Clang
ifeq ($(CC),cl)
$(TARGET_LIB): $(OBJS)
	$(CC) $(LDFLAGS) /Fe:$@ $^

%.obj: %.c
	$(CC) $(CFLAGS) /c /Fo:$@ $<
else
$(TARGET_LIB): $(OBJS)
	@echo "Linking $(TARGET_LIB)"
	$(LD) $(LDFLAGS) -o $@ $^

%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<
endif

# Dependency generation (optional but nice)
$(SRCS:.c=.d): %.d: %.c
	$(CC) $(CFLAGS) -MM -MT $(@:.d=.o) $< > $@

-include $(SRCS:.c=.d)

clean:
	-$(RM) $(TARGET_LIB) $(OBJS) $(SRCS:.c=.d) 2>nul || true
