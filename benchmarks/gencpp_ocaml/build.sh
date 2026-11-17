#!/bin/bash
# Build the Gb* workloads as C++ (from benchmarks/gencpp/out, or $SRC) and as
# OCaml (flambda -O3 and, if present, the vanilla crane-rocq91 switch).
#   build.sh OUTDIR [SRC]
# Run `dune build benchmarks/gencpp benchmarks/gencpp_ocaml` first.
# SKIP_ML=1 builds only the C++ side.
# CXXFLAGS_EXTRA adds to every C++ build; CPP_VARIANTS picks the C++ flag sets
# (O2, O3, O3lto, O3native; an "mi" suffix links mimalloc).
# Each exe takes N ROUNDS: bst 200000 20, lists 4000 10, interp 24 20,
# clo 1000 20000, maps 50000 3.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
CRANE="$(cd "$HERE/../.." && pwd)"
mkdir -p "$1"; OUT="$(cd "$1" && pwd)"
SRC="${2:-$CRANE/benchmarks/gencpp/out/GenCppBench}"
mkdir -p "$OUT"
HB_LLVM=/opt/homebrew/opt/llvm
# CRANE_SDKROOT overrides the SDK both compilers link against.
export SDKROOT="${CRANE_SDKROOT:-${SDKROOT:-$(xcrun --show-sdk-path)}}"; SDK="$SDKROOT"
CXX=("$HB_LLVM/bin/clang++" -std=c++2c -fbracket-depth=1024 -isysroot "$SDK"
     -nostdlib++ -stdlib=libc++ -I"$HB_LLVM/include/c++/v1"
     -iquote "$SRC" -I "$CRANE/theories/cpp" -DNDEBUG)
LINK=(-L"$HB_LLVM/lib/c++" -Wl,-rpath,"$HB_LLVM/lib/c++" -lc++ -lc++abi)
MIMALLOC=(-L/opt/homebrew/lib -lmimalloc)

entry_of() {
  case "$1" in
    bst) echo bst ;; lists) echo lists ;; interp) echo interp ;;
    clo) echo closures ;; maps) echo maps ;;
  esac
}
module_of() {
  case "$1" in
    bst) echo GbBst ;; lists) echo GbLists ;; interp) echo GbInterp ;;
    clo) echo GbClo ;; maps) echo GbMaps ;;
  esac
}

VARIANTS="${CPP_VARIANTS:-O2 O3 O3lto}"
flags_of() {
  case "$1" in
    O2*) echo "-O2" ;;
    O3lto*) echo "-O3 -flto" ;;
    O3native*) echo "-O3 -flto -mcpu=native" ;;
    O3*) echo "-O3" ;;
  esac
}

for w in bst lists interp clo maps; do
  cat > "$OUT/main_$w.cpp" <<EOF
#include "gb_$w.h"
#define WL_CALL(n, r) $(module_of $w)::$(entry_of $w)(n, r)
#include "$CRANE/benchmarks/gencpp/main.cpp"
EOF
  for v in $VARIANTS; do
    extra=()
    [[ "$v" == *mi ]] && extra=("${MIMALLOC[@]}")
    # shellcheck disable=SC2046
    "${CXX[@]}" $(flags_of "$v") ${CXXFLAGS_EXTRA:-} "$OUT/main_$w.cpp" "$SRC/gb_$w.cpp" \
      "${LINK[@]}" ${extra[@]+"${extra[@]}"} -o "$OUT/cpp_${w}_$v.exe" &
  done
done

ML="$CRANE/benchmarks/gencpp_ocaml/out"
for w in bst lists interp clo maps; do
  [ -n "${SKIP_ML:-}" ] && break
  cat > "$OUT/run_$w.ml" <<EOF
let () =
  let n = int_of_string Sys.argv.(1) and r = int_of_string Sys.argv.(2) in
  let t0 = Unix.gettimeofday () in
  let x = Gb_$w.$(module_of $w).$(entry_of $w) n r in
  Printf.printf "%d time=%.4f\n" x (Unix.gettimeofday () -. t0)
EOF
  mkdir -p "$OUT/ml_$w"
  cp "$ML/gb_$w.ml" "$ML/gb_$w.mli" "$OUT/run_$w.ml" "$OUT/ml_$w/"
  (cd "$OUT/ml_$w" &&
   opam exec --switch=crane-rocq91-flambda -- ocamlfind ocamlopt -package unix -linkpkg \
     -O3 gb_$w.mli gb_$w.ml run_$w.ml -o "$OUT/ml_${w}_fl.exe" &&
   if opam switch list -s | grep -qx crane-rocq91; then
     rm -f ./*.cm* ./*.o
     opam exec --switch=crane-rocq91 -- ocamlfind ocamlopt -package unix -linkpkg \
       gb_$w.mli gb_$w.ml run_$w.ml -o "$OUT/ml_${w}_vanilla.exe"
   fi) &
done
wait
ls "$OUT"/*.exe
