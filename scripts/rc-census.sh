#!/bin/bash
# Reference-count census: run the whole test sweep with the counting shared
# pointer (theories/cpp/count_rc.h) and report, per test, how much
# reference-count traffic it performs.
#
# This is Stage 0 of the borrow-inference plan: it says which tests carry the
# traffic a borrow could remove, so the later stages are aimed rather than
# guessed at.
#
# Usage: scripts/rc-census.sh [output.csv]
#
# Columns: test, dups, drops, frees, dups_per_free
#
#   dups           copies of a non-null shared pointer -- one atomic increment
#                  each, and the thing borrow inference removes.
#   frees          drops that took the count to zero, i.e. objects that died.
#                  This traffic is unavoidable: the object has to be destroyed
#                  however the program is compiled.
#   dups_per_free  the read-heaviness proxy the plan asks for.  A test that
#                  allocates and immediately consumes has a ratio near zero and
#                  nothing to win; a test that passes the same structure around
#                  has a high ratio and is where the wins are.
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd -P)"
out="${1:-$root/docs/assets/rc-baseline.csv}"
log="$(mktemp -t crane-rc-census)"

mkdir -p "$(dirname "$out")"

echo "Running the sweep with CRANE_COUNT_RC=1 (this rebuilds every test)..."
cd "$root"
git checkout tests
git clean -fdq tests
rm -rf _build/default/tests
CRANE_COUNT_RC=1 CRANE_RC_LOG="$log" make test || true
# The counting build is not the build anyone should keep: restore the tree.
git checkout tests
git clean -fdq tests

python3 - "$log" "$out" <<'PY'
import re, sys
log, out = sys.argv[1], sys.argv[2]
line = re.compile(
    r"\[count_rc\] (\S+): dups=(\d+) drops=(\d+) frees=(\d+)")
rows = {}
for raw in open(log):
    m = line.match(raw)
    if not m:
        continue
    name, dups, drops, frees = m.group(1), *map(int, m.groups()[1:])
    # A test binary may be run more than once in a sweep; sum the runs.
    d, r, f = rows.get(name, (0, 0, 0))
    rows[name] = (d + dups, r + drops, f + frees)

ranked = sorted(rows.items(), key=lambda kv: -kv[1][0])
with open(out, "w") as fh:
    fh.write("test,dups,drops,frees,dups_per_free\n")
    for name, (d, r, f) in ranked:
        fh.write(f"{name},{d},{r},{f},{d / f if f else 0:.2f}\n")

td, tr, tf = (sum(v[i] for v in rows.values()) for i in range(3))
print(f"\n{len(rows)} tests reported.  Totals: dups={td} drops={tr} frees={tf}")
print(f"Top by dups (written to {out}):\n")
print(f"{'test':<34}{'dups':>12}{'frees':>12}{'dups/free':>11}")
for name, (d, r, f) in ranked[:20]:
    print(f"{name:<34}{d:>12}{f:>12}{d / f if f else 0:>11.2f}")
PY

rm -f "$log"
