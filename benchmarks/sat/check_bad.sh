#!/bin/bash
# Run every solver build on the malformed and edge-case files in inst_bad/
# and compare each answer with inst_bad/expected.txt.  Each run gets 30 s
# and 4 GB, since old drivers looped or allocated without bound on some.
HERE="$(cd "$(dirname "$0")" && pwd)"
SOLVERS=(${SOLVERS:-solver_cpp solver_cpp_checked solver_direct_ml solver_direct_ml_fl solver_ml solver_ml_fl})
fail=0
while read -r name want; do
  for s in "${SOLVERS[@]}"; do
    [ -x "$HERE/build/$s.exe" ] || continue
    got="$( (ulimit -v 4000000 2>/dev/null; perl -e 'alarm 30; exec @ARGV' \
             "$HERE/build/$s.exe" "$HERE/inst_bad/$name.cnf") 2>&1 | tail -1)"
    if [ "${got%% *}" = "$want" ]; then echo "ok   $name $s"
    else echo "FAIL $name $s: want $want, got '$got'"; fail=1; fi
  done
done < "$HERE/inst_bad/expected.txt"
exit $fail
