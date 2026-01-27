#!/bin/bash
# Compile C++ files with BDE libraries using pkg-config
# Usage: compile-bde.sh output.exe source1.cpp source2.cpp ...

set -e

OUTPUT="$1"
shift
SOURCES="$@"

# Find BDE installation via pkg-config
# Users should set PKG_CONFIG_PATH to include BDE's pkgconfig directory
# e.g., export PKG_CONFIG_PATH=/path/to/bde_install/lib/pkgconfig

# Try to auto-detect BDE_PREFIX if not set
if [ -z "$BDE_PREFIX" ]; then
    # Common locations to check
    for prefix in \
        "$HOME/Library/bde_install" \
        "$HOME/bde_install" \
        "/opt/bb" \
        "/usr/local"; do
        if [ -f "$prefix/lib/pkgconfig/bsl.pc" ]; then
            BDE_PREFIX="$prefix"
            break
        fi
    done
fi

if [ -z "$BDE_PREFIX" ]; then
    echo "Error: Cannot find BDE installation." >&2
    echo "Set BDE_PREFIX to your BDE install directory, or" >&2
    echo "set PKG_CONFIG_PATH to include BDE's pkgconfig directory." >&2
    exit 1
fi

export PKG_CONFIG_PATH="$BDE_PREFIX/lib/pkgconfig:$PKG_CONFIG_PATH"

# Get compiler flags from pkg-config, overriding the prefix
BDE_CFLAGS=$(pkg-config --define-variable=prefix="$BDE_PREFIX" --cflags bdl 2>/dev/null || echo "-I$BDE_PREFIX/include")
BDE_LIBS=$(pkg-config --define-variable=prefix="$BDE_PREFIX" --libs bdl --static 2>/dev/null || echo "-L$BDE_PREFIX/lib -lbdl -lbsl -linteldfp -lpcre2 -lryu")

# Compile with C++20, BDE ABI compatibility, and suppress deprecation warnings
exec clang++ \
    -std=c++20 \
    -DBSLS_LIBRARYFEATURES_FORCE_ABI_CPP17 \
    -Wno-deprecated-literal-operator \
    -O2 \
    -I . \
    $BDE_CFLAGS \
    $SOURCES \
    $BDE_LIBS \
    -o "$OUTPUT"
