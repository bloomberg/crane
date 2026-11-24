# Sourced, not run: which external library a test needs, and whether this
# machine has it.  A test's need is read from the compile script its dune rule
# runs (compile-bde.sh, compile-gmp.sh, compile-boost.sh), never from its
# name, so a test named bde_foo and one named foo_bde are treated alike.
#
# The detection mirrors the BDE and GMP compile scripts' search lists; keep
# them in step (compile-boost.sh sources this file instead).
# CRANE_WITHOUT="bde gmp boost" (any subset) pretends a library is absent, to
# rehearse a machine that lacks it.

# test_dep <suite-dune> <test-name>: prints bde, gmp or boost, or nothing for
# a test that needs only the standard library (or has no rule).
test_dep() {
    awk -v name="$2" '
        $0 ~ "^\\(subdir " name "$" { found = 1; next }
        found && /^\(subdir / { exit }
        found && match($0, /compile-(bde|gmp|boost)\.sh/) {
            print substr($0, RSTART + 8, RLENGTH - 11); exit
        }
    ' "$1"
}

# test_dep_table <suite-dune>: one "name:dep" word per test that needs a
# library, for callers that look up many tests of one suite.
test_dep_table() {
    awk '
        /^\(subdir / { name = $2 }
        name != "" && match($0, /compile-(bde|gmp|boost)\.sh/) {
            print name ":" substr($0, RSTART + 8, RLENGTH - 11); name = ""
        }
    ' "$1"
}

_dep_disabled() {
    case " ${CRANE_WITHOUT:-} " in *" $1 "*) return 0 ;; esac
    return 1
}

# find_bde_prefix: as compile-bde.sh.
find_bde_prefix() {
    _dep_disabled bde && return 1
    local prefix
    for prefix in "${BDE_PREFIX:-}" "$HOME/Library/bde_install" "$HOME/bde_install" \
                  /opt/bb /usr/local; do
        if [ -n "$prefix" ] && [ -f "$prefix/lib/pkgconfig/bsl.pc" ]; then
            echo "$prefix"; return 0
        fi
    done
    return 1
}

# find_gmp_prefix: as compile-gmp.sh.
find_gmp_prefix() {
    _dep_disabled gmp && return 1
    local prefix
    for prefix in "${GMP_PREFIX_ENV:-}" /opt/homebrew/opt/gmp /usr/local/opt/gmp \
                  /usr/local /usr; do
        if [ -n "$prefix" ] && [ -f "$prefix/include/gmpxx.h" ]; then
            echo "$prefix"; return 0
        fi
    done
    return 1
}

# find_boost_prefix: compile-boost.sh's search too.
find_boost_prefix() {
    _dep_disabled boost && return 1
    local prefix
    for prefix in "${BOOST_PREFIX:-}" /opt/homebrew/opt/boost /opt/homebrew \
                  /usr/local /usr; do
        if [ -n "$prefix" ] && [ -f "$prefix/include/boost/multiprecision/cpp_int.hpp" ]; then
            echo "$prefix"; return 0
        fi
    done
    return 1
}

# dep_include_dir <prefix>: the include directory to add for a library
# installed at <prefix>, or nothing for /usr.  The compiler already searches
# /usr/include, after the C++ standard library's own directories; naming it
# again (-isystem, CPLUS_INCLUDE_PATH) moves it ahead of them, and their
# [#include_next <math.h>] then finds nothing.
dep_include_dir() {
    [ "$1" = /usr ] || echo "$1/include"
}

# dep_prefix <bde|gmp|boost>: the install prefix, or failure if absent.
dep_prefix() {
    case "$1" in
        bde) find_bde_prefix ;;
        gmp) find_gmp_prefix ;;
        boost) find_boost_prefix ;;
        *) return 1 ;;
    esac
}
