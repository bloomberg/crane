#!/bin/bash
# Compile every generated public header as the first and only include of a
# translation unit, with no precompiled header and no test driver in front of
# it.  The test build includes crane_pch.h ahead of everything, which hides a
# header that forgot an include; this does not.  It also rejects reserved
# identifiers in generated code ([_Upper], [a__b]): the runtime headers are
# included as system headers, so only what Crane generated is judged.
#
# Usage: scripts/check-headers-standalone.sh [suite-dir ...]
#   (default: tests/basics tests/monadic tests/regression)
#
# Prints one line per failing header and exits nonzero if there was one.

set -u
PROJECT_ROOT="$(cd "$(dirname "$0")/.." && pwd -P)"
THEORIES_CPP="$PROJECT_ROOT/theories/cpp"
JOBS="${JOBS:-8}"

HB_LLVM="${HB_LLVM:-/opt/homebrew/opt/llvm}"
if [ -d "$HB_LLVM" ]; then
    CXX="$HB_LLVM/bin/clang++"
    FLAGS=(-nostdlib++ -stdlib=libc++ -I"$HB_LLVM/include/c++/v1")
    if [ "$(uname)" = "Darwin" ]; then
        SDK="${SDKROOT:-$(xcrun --show-sdk-path 2>/dev/null)}"
        [ -n "$SDK" ] && FLAGS+=(-isysroot "$SDK")
    fi
else
    CXX="clang++"
    FLAGS=()
fi
FLAGS+=(-std=c++2c -fsyntax-only -fbracket-depth=1024 -isystem "$THEORIES_CPP"
        -Werror=reserved-identifier)

if [ $# -eq 0 ]; then
    set -- "$PROJECT_ROOT/tests/basics" "$PROJECT_ROOT/tests/monadic" \
           "$PROJECT_ROOT/tests/regression"
fi

# A generated header is one Crane wrote: it opens with Crane's include guard.
# Hand-written support headers in a test directory are not its business, and
# neither are the tests that need BDE or GMP installed (*_bde, *_gmp), which
# CI skips for the same reason.
headers=()
for suite in "$@"; do
    while IFS= read -r h; do
        case "$(basename "$(dirname "$h")")" in *_bde | *_gmp) continue ;; esac
        head -5 "$h" | grep -q '^#ifndef INCLUDED_' && headers+=("$h")
    done < <(find "$suite" -mindepth 2 -maxdepth 2 -name '*.h' | sort)
done

check_one() {
    local h="$1"
    local out
    if ! out=$(printf '#include "%s"\n' "$(basename "$h")" |
               "$CXX" "${FLAGS[@]}" -I "$(dirname "$h")" -x c++ - 2>&1); then
        printf 'FAIL %s: %s\n' "${h#"$PROJECT_ROOT"/}" \
               "$(printf '%s\n' "$out" | grep -m1 'error:' | sed 's/^.*error: //')"
        return 1
    fi
}
export -f check_one
export CXX PROJECT_ROOT
export FLAGS_STR="${FLAGS[*]}"

failures=$(printf '%s\n' "${headers[@]}" |
    xargs -P "$JOBS" -I{} bash -c 'FLAGS=($FLAGS_STR); check_one "$1"' _ {})
n=${#headers[@]}
if [ -n "$failures" ]; then
    printf '%s\n' "$failures" | sort
    echo "$(printf '%s\n' "$failures" | wc -l | tr -d ' ') of $n headers fail standalone"
    exit 1
fi
echo "all $n headers compile standalone"
