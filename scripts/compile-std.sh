#!/bin/bash
# Compile C++ files with proper libc++ linking for Homebrew LLVM
# Usage: compile-std.sh <project_root> output.exe source1.cpp source2.cpp ...

set -e

# Resolve project root to absolute path
PROJECT_ROOT="$(cd "$1" && pwd -P)"
shift

# If we're in the build directory (_build/default), go up to source root
if [[ "$PROJECT_ROOT" == */_build/default ]]; then
    PROJECT_ROOT="${PROJECT_ROOT%/_build/default}"
fi

THEORIES_CPP="$PROJECT_ROOT/theories/cpp"

OUTPUT="$1"
shift
SOURCES="$@"

# Optimization level: O0 (default, fast compile), O1, O2, or O3
OPT_LEVEL="${CRANE_CPP_OPTIMIZATION:-O0}"

# Precompiled header support
PCH_SRC="$THEORIES_CPP/crane_pch.h"
DEFAULT_PCH_DIR="$PROJECT_ROOT/_build/pch"
if [ "${GITHUB_ACTIONS:-}" = "true" ]; then
    DEFAULT_PCH_DIR="${RUNNER_TEMP:-${TMPDIR:-/tmp}}/crane-pch"
fi
PCH_DIR="${CRANE_PCH_DIR:-$DEFAULT_PCH_DIR}"
PCH_FILE="$PCH_DIR/crane_pch_${OPT_LEVEL}.h.pch"

# Detect Homebrew LLVM
HB_LLVM="${HB_LLVM:-/opt/homebrew/opt/llvm}"

# Build the compiler command
if [ -d "$HB_LLVM" ]; then
    CXX="$HB_LLVM/bin/clang++"
    # On macOS, Homebrew clang may not find the SDK automatically
    SYSROOT_FLAGS=()
    if [ "$(uname)" = "Darwin" ]; then
        SDK="${SDKROOT:-$(xcrun --show-sdk-path 2>/dev/null)}"
        if [ -n "$SDK" ] && [ -d "$SDK" ]; then
            SYSROOT_FLAGS=(-isysroot "$SDK")
        fi
    fi
    CXX_FLAGS=(
        -std=c++23
        -"$OPT_LEVEL"
        -fbracket-depth=1024
        "${SYSROOT_FLAGS[@]}"
        -I .
        -I "$THEORIES_CPP"
        -nostdlib++
        -stdlib=libc++
        -I"$HB_LLVM/include/c++/v1"
        -Wall -Wextra -Wpedantic -Wconversion -Wfloat-conversion
        -Wsign-conversion -Wstring-compare -Wformat-overflow
        -Wno-stringop-overflow -Wstringop-overflow -Wstringop-overflow=4
        -Wno-unknown-warning-option -Wno-unused-function
        -Wno-unused-local-typedef -Wno-shorten-64-to-32
        -Wno-unused-variable -Wno-unused-value
        -Wno-constant-conversion -Wno-sign-conversion
        -Wno-implicit-int-conversion -Werror
    )
    LINK_FLAGS=(
        -L"$HB_LLVM/lib"
        -L"$HB_LLVM/lib/c++"
        -Wl,-rpath,"$HB_LLVM/lib"
        -Wl,-rpath,"$HB_LLVM/lib/c++"
        -lc++ -lc++abi
    )
else
    CXX="clang++"
    CXX_FLAGS=(
        -std=c++23
        -"$OPT_LEVEL"
        -fbracket-depth=1024
        -I .
        -I "$THEORIES_CPP"
        -Wall -Wextra -Wpedantic -Wconversion -Wfloat-conversion
        -Wsign-conversion -Wstring-compare -Wformat-overflow
        -Wno-stringop-overflow -Wstringop-overflow -Wstringop-overflow=4
        -Wno-unknown-warning-option -Wno-unused-function
        -Wno-unused-local-typedef -Wno-shorten-64-to-32
        -Wno-unused-variable -Wno-unused-value
        -Wno-constant-conversion -Wno-sign-conversion
        -Wno-implicit-int-conversion -Werror
    )
    LINK_FLAGS=()
fi

# Build PCH if it doesn't exist or is older than the source
if [ -f "$PCH_SRC" ] && { [ ! -f "$PCH_FILE" ] || [ "$PCH_SRC" -nt "$PCH_FILE" ]; }; then
    if mkdir -p "$PCH_DIR" 2>/dev/null; then
        "$CXX" -x c++-header "${CXX_FLAGS[@]}" "$PCH_SRC" -o "$PCH_FILE" 2>/dev/null || true
    fi
fi

# Use PCH if available
PCH_FLAGS=()
if [ -f "$PCH_FILE" ]; then
    PCH_FLAGS=(-include-pch "$PCH_FILE")
fi

exec "$CXX" "${CXX_FLAGS[@]}" "${PCH_FLAGS[@]}" $SOURCES "${LINK_FLAGS[@]}" -o "$OUTPUT"
