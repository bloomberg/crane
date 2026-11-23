#!/usr/bin/env bash
# Report the entries of unit_tests/typed_fit_allowlist.txt a census no
# longer hits.
#
# The typed-fit check (Core_to_cpp.Typed_checks.fit) fails extraction under
# CRANE_CHECK_IR on any pair not on the allowlist, so the list cannot grow.
# It shrinks by hand: after a full extraction under CRANE_PROBE, every
# allowed pair that fired is a `typed-fit-allowed` line of the log, and an
# entry with none is a defect fixed (or a test removed) whose line can go.
#
#   CRANE_PROBE=/tmp/probe.log make extract   # from clean, every folder
#   scripts/check-typed-fit-allowlist.sh /tmp/probe.log
#
# Entries after the "# loopify census only" header are hit only with Loopify
# on everywhere (scripts/loopify-census.sh) and are not checked here.
#
# Exits 1 when some entry is stale.
set -euo pipefail
log=${1:?usage: $0 <CRANE_PROBE log of a full extraction>}
list="$(dirname "$0")/../unit_tests/typed_fit_allowlist.txt"
stale=$(comm -23 \
  <(sed '/^# loopify census only/,$d' "$list" | grep -v '^#' | grep -v '^$' | LC_ALL=C sort -u) \
  <(sed -n 's/^typed-fit-allowed //p' "$log" | LC_ALL=C sort -u))
if [ -n "$stale" ]; then
  echo "typed-fit allowlist: $(printf '%s\n' "$stale" | wc -l | tr -d ' ') stale entries (delete them):"
  printf '%s\n' "$stale"
  exit 1
fi
echo "typed-fit allowlist: every entry is hit"
