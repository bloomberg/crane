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
if [ -n "${CXX:-}" ]; then
    FLAGS=()
elif [ -d "$HB_LLVM" ]; then
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
COMMON=(-fsyntax-only -fbracket-depth=1024 -DCRANE_STRICT_ARITY -Werror=reserved-identifier)
STD_FLAGS=("${FLAGS[@]}" -std=c++2c "${COMMON[@]}" -isystem "$THEORIES_CPP")

if [ $# -eq 0 ]; then
    set -- "$PROJECT_ROOT/tests/basics" "$PROJECT_ROOT/tests/monadic" \
           "$PROJECT_ROOT/tests/regression"
fi

# shellcheck source=test-deps.sh
. "$PROJECT_ROOT/scripts/test-deps.sh"

# The flags a header is checked under follow the library its test's dune rule
# compiles against (scripts/test-deps.sh): BDE's flavour is C++20 with
# theories/cpp_bde shadowing theories/cpp, as compile-bde.sh builds it.  A
# test whose library this machine lacks is skipped, and said so.
# (Plain variables, not an associative array: macOS ships bash 3.2.)
export DEP_FLAGS_std="${STD_FLAGS[*]}"
missing=" "
for dep in gmp boost bde; do
    if prefix=$(dep_prefix "$dep"); then
        case "$dep" in
            bde) DEP_FLAGS_bde="${FLAGS[*]} -std=c++20 ${COMMON[*]}"
                 DEP_FLAGS_bde+=" -DBSLS_LIBRARYFEATURES_FORCE_ABI_CPP17"
                 DEP_FLAGS_bde+=" -isystem $PROJECT_ROOT/theories/cpp_bde"
                 DEP_FLAGS_bde+=" -isystem $THEORIES_CPP -isystem $prefix/include"
                 export DEP_FLAGS_bde ;;
            *) inc=$(dep_include_dir "$prefix")
               export "DEP_FLAGS_$dep=${STD_FLAGS[*]}${inc:+ -isystem $inc}" ;;
        esac
    else
        missing+="$dep "
    fi
done

# A generated header is one Crane wrote: it opens with [#pragma once] and has
# the implementation file Crane writes beside it.  Hand-written support
# headers in a test directory are not its business.
jobs=()
skipped=()
for suite in "$@"; do
    table=$(test_dep_table "$suite/dune" 2>/dev/null)
    while IFS= read -r h; do
        [ -f "${h%.h}.cpp" ] && head -2 "$h" | grep -qx '#pragma once' || continue
        test_name=$(basename "$(dirname "$h")")
        dep=std
        for entry in $table; do
            [ "${entry%:*}" = "$test_name" ] && dep=${entry#*:} && break
        done
        if [[ "$missing" == *" $dep "* ]]; then
            skipped+=("SKIP ${h#"$PROJECT_ROOT"/}: needs $dep, not found")
            continue
        fi
        jobs+=("$dep $h")
    done < <(find "$suite" -mindepth 2 -maxdepth 2 -name '*.h' | sort)
done

check_one() {
    local dep="${1%% *}" h="${1#* }"
    local -a flags
    read -ra flags <<< "$(printenv "DEP_FLAGS_$dep")"
    local out
    if ! out=$(printf '#include "%s"\n' "$(basename "$h")" |
               "$CXX" "${flags[@]}" -I "$(dirname "$h")" -x c++ - 2>&1); then
        printf 'FAIL %s: %s\n' "${h#"$PROJECT_ROOT"/}" \
               "$(printf '%s\n' "$out" | grep -m1 'error:' | sed 's/^.*error: //')"
        return 1
    fi
}
export -f check_one
export CXX PROJECT_ROOT

[ ${#skipped[@]} -gt 0 ] && printf '%s\n' "${skipped[@]}"
failures=
[ ${#jobs[@]} -gt 0 ] && failures=$(printf '%s\n' "${jobs[@]}" |
    xargs -P "$JOBS" -I{} bash -c 'check_one "$1"' _ {})
n=${#jobs[@]}
if [ -n "$failures" ]; then
    printf '%s\n' "$failures" | sort
    echo "$(printf '%s\n' "$failures" | wc -l | tr -d ' ') of $n headers fail standalone"
    exit 1
fi
echo "all $n headers compile standalone (${#skipped[@]} skipped)"
