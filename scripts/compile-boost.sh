#!/usr/bin/env bash
# Compile C++ files that include Boost headers (header-only libraries such as
# boost::multiprecision): compile-std.sh with Boost's include directory on the
# system include path, so that Boost's own headers are exempt from -Werror.
# Usage: compile-boost.sh <project_root> output.exe source1.cpp source2.cpp ...
# Without Boost, writes a stub that reports the test skipped.

set -e

BOOST_INCLUDE=""
for prefix in "${BOOST_PREFIX:-}" /opt/homebrew/opt/boost /opt/homebrew /usr/local /usr; do
    if [ -n "$prefix" ] && [ -f "$prefix/include/boost/multiprecision/cpp_int.hpp" ]; then
        BOOST_INCLUDE="$prefix/include"
        break
    fi
done

if [ -z "$BOOST_INCLUDE" ]; then
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

export CPLUS_INCLUDE_PATH="$BOOST_INCLUDE${CPLUS_INCLUDE_PATH:+:$CPLUS_INCLUDE_PATH}"
exec "$(dirname "$0")/compile-std.sh" "$@"
