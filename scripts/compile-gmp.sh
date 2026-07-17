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
# Keep the source operands as a real array so they reach the compiler as
# distinct argv entries. Never re-expand them as an unquoted scalar: word
# splitting would let a source path containing spaces/metacharacters, or one
# beginning with '-', turn into extra compiler options (CWE-88 / CWE-78).
SOURCES=("$@")

# Reject any operand that clang would interpret as an option rather than an
# input file: '-foo' is a flag and '@foo' is a response file, regardless of
# quoting. Generated C++ sources never legitimately start with these.
for _src in "${SOURCES[@]}"; do
    case "$_src" in
        -* | @*)
            echo "Error: refusing source operand that could be read as a compiler option: '$_src'" >&2
            exit 1
            ;;
    esac
done

# Optimization level: O0 (default, fast compile), O1, O2, or O3. Validated
# against a fixed allow-list because it is attacker-influenced (an environment
# variable) and is spliced directly onto the compiler command line.
OPT_LEVEL="${CRANE_CPP_OPTIMIZATION:-O0}"
case "$OPT_LEVEL" in
    O0 | O1 | O2 | O3) ;;
    *)
        echo "Error: invalid CRANE_CPP_OPTIMIZATION='$OPT_LEVEL' (expected O0, O1, O2, or O3)" >&2
        exit 1
        ;;
esac

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

exec "$CXX" "${CXX_FLAGS[@]}" "${SANITIZE_FLAGS[@]}" "${SOURCES[@]}" "${LINK_FLAGS[@]}" "${SANITIZE_FLAGS[@]}" -o "$OUTPUT"
