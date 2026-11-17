#!/bin/bash
# Time every solver build on every instance in inst/; median of REPS runs.
# Each binary times only its solve call (not parsing, extraction or
# compilation).  Writes results.csv: instance,solver,result,conflicts,median_s
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
REPS="${REPS:-3}"
SOLVERS=(solver_cpp solver_direct_ml_fl solver_direct_ml solver_ml_fl solver_ml)
OUT="$HERE/results.csv"
echo "instance,solver,result,conflicts,median_s" > "$OUT"
for f in "$HERE"/inst/*.cnf; do
  name="$(basename "$f" .cnf)"
  for s in "${SOLVERS[@]}"; do
    times=()
    for _ in $(seq "$REPS"); do
      line="$("$HERE/build/$s.exe" "$f")"
      res="${line%% *}"
      confl="$(sed -E 's/.*conflicts=([0-9]+).*/\1/' <<<"$line")"
      times+=("$(sed -E 's/.*time=([0-9.]+).*/\1/' <<<"$line")")
    done
    med="$(printf '%s\n' "${times[@]}" | sort -g | awk '{a[NR]=$1} END {print a[int((NR+1)/2)]}')"
    echo "$name,$s,$res,$confl,$med" | tee -a "$OUT"
  done
done
