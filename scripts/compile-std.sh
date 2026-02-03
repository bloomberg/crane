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

# Detect Homebrew LLVM
HB_LLVM="${HB_LLVM:-/opt/homebrew/opt/llvm}"

if [ -d "$HB_LLVM" ]; then
    # Use Homebrew LLVM with explicit libc++ linking
    exec "$HB_LLVM/bin/clang++" \
        -std=c++23 \
        -O2 \
        -fbracket-depth=1024 \
        -I . \
        -I "$THEORIES_CPP" \
        -nostdlib++ \
        -stdlib=libc++ \
        -I"$HB_LLVM/include/c++/v1" \
        -L"$HB_LLVM/lib" \
        -L"$HB_LLVM/lib/c++" \
        -Wl,-rpath,"$HB_LLVM/lib" \
        -Wl,-rpath,"$HB_LLVM/lib/c++" \
        $SOURCES \
        -lc++ -lc++abi \
        -o "$OUTPUT"
else
    # Fallback to system clang++
    exec clang++ -std=c++23 -O2 -fbracket-depth=1024 -I . -I "$THEORIES_CPP" $SOURCES -o "$OUTPUT"
fi
