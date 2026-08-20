#!/usr/bin/env bash
# Report which recursive functions the loopify pass fails to linearise.
#
# Builds the whole test corpus with loopify diagnostics on and collects every
# function the pass declined. The result is compared against the checked-in
# baseline in tests/loopify-coverage.golden, so the set of declines is a
# tracked artifact: it can only change deliberately.
#
#   scripts/loopify-coverage.sh           # check against the baseline
#   scripts/loopify-coverage.sh --accept  # rewrite the baseline
#
# A decline means the emitted C++ function still calls itself and will grow
# the C++ stack, which is the whole thing loopify exists to prevent. Adding a
# new one is a regression even though every runtime test still passes.

set -uo pipefail

cd "$(dirname "$0")/.."

GOLDEN=tests/loopify-coverage.golden
ACTUAL=$(mktemp)
trap 'rm -f "$ACTUAL"' EXIT

# Diagnostics are printed by coqc as it extracts, so a cached .vo prints
# nothing and the report would silently cover only whatever happened to
# rebuild. Drop the .vo files to force every extraction to run again.
# (dune --force does not help: it re-runs the requested action, not the
# transitive ones that actually emit the diagnostics.)
echo "Forcing re-extraction of the test corpus..." >&2
find _build/default/tests -name '*.vo' -delete 2>/dev/null

echo "Building test corpus with loopify diagnostics..." >&2
CRANE_LOOPIFY_DIAGNOSTICS=1 dune build \
  tests/basics tests/monadic tests/regression tests/wip 2>&1 |
  grep '^\[loopify\] .*DECLINED' |
  sed 's/^\[loopify\] //' |
  sort -u > "$ACTUAL"

if [ "${1:-}" = "--accept" ]; then
  cp "$ACTUAL" "$GOLDEN"
  echo "Wrote $(wc -l < "$GOLDEN" | tr -d ' ') declines to $GOLDEN" >&2
  exit 0
fi

if diff -u "$GOLDEN" "$ACTUAL"; then
  echo "loopify coverage unchanged: $(wc -l < "$ACTUAL" | tr -d ' ') declines" >&2
  exit 0
fi

cat >&2 <<'MSG'

loopify coverage changed.
  Lines starting '-' are declines that are now fixed  -> run with --accept.
  Lines starting '+' are newly declined functions     -> a regression.
MSG
exit 1
