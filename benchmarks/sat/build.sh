#!/bin/bash
# Extract (via dune) and compile both solvers into build/.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
CRANE="$(cd "$HERE/../.." && pwd)"
(cd "$CRANE" && dune build benchmarks/sat 2>&1 | grep -v -i "deprecat\|Hint:\|warnings (\|Please upgrade" || true)
mkdir -p "$HERE/build"
cd "$HERE/build"
cp "$HERE"/out/SatBench/solver.{h,cpp} "$HERE"/{sat_vec.h,solver_main.cpp,solver_checked.cpp} .
CRANE_CPP_OPTIMIZATION="${OPT:-O2}" "$CRANE/scripts/compile-std.sh" "$CRANE" solver_cpp.exe solver.cpp solver_main.cpp
# Not benchmarked: bounds checks plus ASan/UBSan, for testing memory safety.
CRANE_CPP_OPTIMIZATION=O1 CRANE_CPP_SANITIZE=1 "$CRANE/scripts/compile-std.sh" "$CRANE" solver_cpp_checked.exe solver_checked.cpp
cp "$HERE"/out/solver_ml.ml{,i} "$HERE"/out/solver_direct_ml.ml{,i} \
   "$HERE"/{vec_impl.ml,itree_run.ml,direct.ml,solver_main_common.ml,solver_main.ml,solver_direct_main.ml} .
OCAMLOPT=(ocamlfind ocamlopt -package unix -linkpkg -unsafe -inline 200)
"${OCAMLOPT[@]}" vec_impl.ml solver_main_common.ml solver_ml.mli solver_ml.ml itree_run.ml solver_main.ml -o solver_ml.exe
"${OCAMLOPT[@]}" vec_impl.ml solver_main_common.ml direct.ml solver_direct_ml.mli solver_direct_ml.ml solver_direct_main.ml -o solver_direct_ml.exe
# The same two OCaml programs under flambda -O3 (opam switch sat-flambda),
# OCaml's most aggressive inliner.
if opam switch list -s 2>/dev/null | grep -qx sat-flambda; then
  FL=(opam exec --switch=sat-flambda -- ocamlfind ocamlopt -package unix -linkpkg -O3 -unsafe -inline 200)
  "${FL[@]}" vec_impl.ml solver_main_common.ml solver_ml.mli solver_ml.ml itree_run.ml solver_main.ml -o solver_ml_fl.exe
  "${FL[@]}" vec_impl.ml solver_main_common.ml direct.ml solver_direct_ml.mli solver_direct_ml.ml solver_direct_main.ml -o solver_direct_ml_fl.exe
fi
