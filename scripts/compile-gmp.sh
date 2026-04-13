#!/bin/bash
# Compile C++ files with GMP (GNU Multiple Precision) library
# Usage: compile-gmp.sh <project_root> output.exe source1.cpp source2.cpp ...

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

# Find GMP installation
GMP_PREFIX=""
if [ -n "$GMP_PREFIX_ENV" ]; then
    GMP_PREFIX="$GMP_PREFIX_ENV"
else
    # Try Homebrew on macOS
    for prefix in \
        "/opt/homebrew/opt/gmp" \
        "/usr/local/opt/gmp" \
        "/usr/local" \
        "/usr"; do
        if [ -f "$prefix/include/gmpxx.h" ]; then
            GMP_PREFIX="$prefix"
            break
        fi
    done
fi

if [ -z "$GMP_PREFIX" ]; then
    if [ -n "$CI" ] || [ -n "$SKIP_GMP_TESTS" ]; then
        echo "GMP not found, creating skip stub for $OUTPUT" >&2
        cat > "$OUTPUT.cpp" << 'STUB_EOF'
#include <iostream>
int main() { std::cout << "SKIPPED: GMP not available\n"; return 0; }
STUB_EOF
        clang++ -std=c++20 -o "$OUTPUT" "$OUTPUT.cpp"
        rm -f "$OUTPUT.cpp"
        exit 0
    fi
    echo "Error: Cannot find GMP installation (gmpxx.h not found)." >&2
    echo "Install GMP with C++ bindings, e.g.: brew install gmp" >&2
    exit 1
fi

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
        -I "$GMP_PREFIX/include"
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
        -Wno-deprecated-literal-operator
        -Wno-deprecated-declarations -Werror
    )
    LINK_FLAGS=(
        -L"$HB_LLVM/lib"
        -L"$HB_LLVM/lib/c++"
        -L"$GMP_PREFIX/lib"
        -Wl,-rpath,"$HB_LLVM/lib"
        -Wl,-rpath,"$HB_LLVM/lib/c++"
        -lc++ -lc++abi
        -lgmpxx -lgmp
    )
else
    CXX="clang++"
    CXX_FLAGS=(
        -std=c++23
        -"$OPT_LEVEL"
        -fbracket-depth=1024
        -I .
        -I "$THEORIES_CPP"
        -I "$GMP_PREFIX/include"
        -Wall -Wextra -Wpedantic -Wconversion -Wfloat-conversion
        -Wsign-conversion -Wstring-compare -Wformat-overflow
        -Wno-stringop-overflow -Wstringop-overflow -Wstringop-overflow=4
        -Wno-unknown-warning-option -Wno-unused-function
        -Wno-unused-local-typedef -Wno-shorten-64-to-32
        -Wno-unused-variable -Wno-unused-value
        -Wno-constant-conversion -Wno-sign-conversion
        -Wno-deprecated-literal-operator
        -Wno-deprecated-declarations -Werror
    )
    LINK_FLAGS=(
        -L"$GMP_PREFIX/lib"
        -lgmpxx -lgmp
    )
fi

# Sanitizer support
SANITIZE_FLAGS=()
if [ "${CRANE_CPP_SANITIZE:-}" = "1" ]; then
    SANITIZE_FLAGS=(
        -fsanitize=address,undefined
        -fno-sanitize-recover=all
        -fno-omit-frame-pointer
    )
fi

exec "$CXX" "${CXX_FLAGS[@]}" "${SANITIZE_FLAGS[@]}" $SOURCES "${LINK_FLAGS[@]}" "${SANITIZE_FLAGS[@]}" -o "$OUTPUT"
