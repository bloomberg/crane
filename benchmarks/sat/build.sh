#!/bin/bash
# Extract the solver (via dune: Crane to C++, stock extraction to OCaml),
# check its proofs, and compile both into build/.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
CRANE="$(cd "$HERE/../.." && pwd)"
dune build --root "$CRANE" benchmarks/sat 2>&1 \
  | grep -v -i "deprecat\|Hint:\|warnings (\|Please upgrade\|Entering directory\|Leaving directory" || true
mkdir -p "$HERE/build"
cd "$HERE/build"
cp "$HERE"/out/SatBench/solver.{h,cpp} "$HERE"/solver_main.cpp .
CRANE_CPP_OPTIMIZATION="${OPT:-O2}" "$CRANE/scripts/compile-std.sh" "$CRANE" solver_cpp.exe solver.cpp solver_main.cpp
# Not benchmarked: the same program under ASan/UBSan.  Global arrays are
# unchecked, so ASan catches any access past an array's end.
CRANE_CPP_OPTIMIZATION=O1 CRANE_CPP_SANITIZE=1 "$CRANE/scripts/compile-std.sh" "$CRANE" solver_cpp_checked.exe solver.cpp solver_main.cpp
cp "$HERE"/out/solver_ml.ml{,i} "$HERE"/{sat_rt.ml,solver_main.ml} .
ocamlfind ocamlopt -package unix -linkpkg -O3 -unsafe -inline 200 \
  sat_rt.ml solver_ml.mli solver_ml.ml solver_main.ml -o solver_ml.exe
