#!/usr/bin/env bash
# Compile C++ files that include Boost headers (header-only libraries such as
# boost::multiprecision): compile-std.sh with Boost's include directory on the
# system include path, so that Boost's own headers are exempt from -Werror.
# Boost under /usr needs nothing: /usr/include is a system directory already.
# Usage: compile-boost.sh <project_root> output.exe source1.cpp source2.cpp ...
# Without Boost, writes a stub that reports the test skipped.

set -e

# The search is test-deps.sh's and the compile is compile-std.sh's, both read
# from the source tree (as compile-std.sh reads theories/cpp): a dune rule
# copies only the script it runs into _build.
SOURCE_ROOT="$(cd "$1" && pwd -P)"
SOURCE_ROOT="${SOURCE_ROOT%/_build/default}"
# shellcheck source=test-deps.sh
. "$SOURCE_ROOT/scripts/test-deps.sh"

if ! BOOST_PREFIX_FOUND=$(find_boost_prefix); then
    OUTPUT="$2"
    echo "Boost not found, creating skip stub for $OUTPUT" >&2
    cat > "$OUTPUT.cpp" << 'STUB_EOF'
#include <iostream>
int main() { std::cout << "SKIPPED: Boost not available\n"; return 0; }
STUB_EOF
    clang++ -std=c++20 -o "$OUTPUT" "$OUTPUT.cpp"
    rm -f "$OUTPUT.cpp"
    exit 0
fi

BOOST_INCLUDE=$(dep_include_dir "$BOOST_PREFIX_FOUND")
if [ -n "$BOOST_INCLUDE" ]; then
    export CPLUS_INCLUDE_PATH="$BOOST_INCLUDE${CPLUS_INCLUDE_PATH:+:$CPLUS_INCLUDE_PATH}"
fi
exec "$SOURCE_ROOT/scripts/compile-std.sh" "$@"
