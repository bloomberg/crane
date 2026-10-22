#!/usr/bin/env bash
# Check the recursion plan against Loopify on every function in the corpus.
#
# Loopify is opt-in, so an ordinary test run checks the recursion plan only
# against the few functions that ask for it.  This extracts the basics,
# monadic and regression tests again with Loopify on everywhere
# (CRANE_LOOPIFY_CENSUS), records what the IR checks report instead of
# failing on it, and compares the result with tests/loopify-census.golden,
# so the set of known disagreements can only change deliberately.
#
#   scripts/loopify-census.sh           # check against the baseline
#   scripts/loopify-census.sh --accept  # rewrite the baseline
#
# The census writes no generated files, and builds in its own build
# directory: its .vo files say nothing about the committed output, which an
# ordinary build must not take as up to date.  The variable is not one dune
# tracks, so the cache is off and the .vo files are removed first; a test
# that does not build is reported as failing.

set -uo pipefail

cd "$(dirname "$0")/.."

GOLDEN=tests/loopify-census.golden
# dune takes a build directory inside _build only as an absolute path.
BUILD=$PWD/_build/census
# Nor does it make the directory that build directory is in.
mkdir -p "$PWD/_build"
LOG=$(mktemp)
OUT=$(mktemp)
ACTUAL=$(mktemp)
trap 'rm -f "$LOG" "$OUT" "$ACTUAL"' EXIT

sources=$(ls tests/basics/*/*.v tests/monadic/*/*.v tests/regression/*/*.v)
targets=$(echo "$sources" | sed 's/\.v$/.vo/')

find "$BUILD/default/tests" -name '*.vo' -delete 2>/dev/null

echo "Extracting the test corpus with Loopify on everywhere..." >&2
# The plugin is installed first, on its own: coqc loads it from the install
# directory, which dune's rules for the theories and the tests do not wait
# for in a build directory of its own.  A run that started one too early
# reports the plugin unavailable but still installs it, so the install is
# tried twice; a real failure fails both times.
if ! dune build --build-dir "$BUILD" @install > "$OUT" 2>&1 &&
  ! dune build --build-dir "$BUILD" @install > "$OUT" 2>&1; then
  cat "$OUT" >&2
  exit 1
fi
# shellcheck disable=SC2086
CRANE_LOOPIFY_CENSUS=$LOG dune build --build-dir "$BUILD" --cache=disabled \
  $targets > "$OUT" 2>&1

units=$(grep -c '^extracted: ' "$LOG")
if [ "$units" -eq 0 ]; then
  echo "loopify census: no unit was extracted; the census did not run" >&2
  exit 1
fi

{
  grep -v '^extracted: ' "$LOG"
  for v in $sources; do
    [ -f "$BUILD/default/${v%.v}.vo" ] || echo "does not build: $v"
  done
} | sort -u > "$ACTUAL"

if grep -q '^does not build: ' "$ACTUAL"; then
  grep -B1 -A8 '^Error' "$OUT" >&2
fi

if [ "${1:-}" = "--accept" ]; then
  cp "$ACTUAL" "$GOLDEN"
  echo "Wrote $(wc -l < "$GOLDEN" | tr -d ' ') findings to $GOLDEN" >&2
  exit 0
fi

if diff -u "$GOLDEN" "$ACTUAL"; then
  echo "loopify census unchanged: $(wc -l < "$ACTUAL" | tr -d ' ') findings in $units units" >&2
  exit 0
fi

cat >&2 <<'MSG'

loopify census changed.
  Lines starting '-' are findings that are now gone  -> run with --accept.
  Lines starting '+' are new findings                -> a regression.
MSG
exit 1
