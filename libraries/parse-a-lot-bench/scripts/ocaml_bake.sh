#!/usr/bin/env bash
# ocaml_bake.sh [harness-dir]
#
# The OCaml side of CraneExtraction.v's [Crane Bake]: bakes the three lexers'
# rule tables ([JSON.json_srules], [CSV.csv_srules], [XML.xml_srules], each
# lexer's rules with their DFAs built) into the plain OCaml extraction in
# <harness>/extracted, so the runners read them at startup instead of building
# them.  Run after `make coq-extract`, before `dune build`.
#
# 1. Builds, in a scratch dune project, a program linking the extracted code as
#    it is, which computes the three values and writes them, Marshalled with
#    sharing kept, as string literals to extracted/baked_srules.ml.
# 2. Rewrites each definition in extracted/{JSON,CSV,XML}.ml to unmarshal its
#    literal (the .mli keeps its type).
#
# Idempotent only on a fresh extraction: it refuses a file already baked.
set -euo pipefail
H=$(cd "${1:-$(dirname "$0")/..}" && pwd)
X=$H/extracted
for m in JSON CSV XML; do
  if grep -q 'Baked_srules' "$X/$m.ml"; then echo "ocaml_bake: $X/$m.ml is already baked" >&2; exit 1; fi
done
T=$(mktemp -d "${TMPDIR:-/tmp}/ocaml_bake.XXXXXX")
trap 'rm -rf "$T"' EXIT
cp -R "$X" "$T/extracted"
cp "$H/native_map_impl.ml" "$T/"
cat > "$T/dune-project" <<'DP'
(lang dune 3.0)
DP
cat > "$T/dune" <<'DU'
(executable (name bake_srules) (flags (:standard -w -a)))
(include_subdirs unqualified)
DU
cat > "$T/bake_srules.ml" <<'ML'
let () =
  let oc = open_out_bin Sys.argv.(1) in
  let emit name v = Printf.fprintf oc "let %s = %S\n" name (Marshal.to_string v []) in
  output_string oc "(* Baked by scripts/ocaml_bake.sh: the lexers' rule tables, Marshalled. *)\n";
  emit "json" JSON.json_srules;
  emit "csv" CSV.csv_srules;
  emit "xml" XML.xml_srules;
  close_out oc
ML
dune build --root "$T" ./bake_srules.exe 2>&1 | grep -v '^Entering\|^Leaving' || true
"$T/_build/default/bake_srules.exe" "$X/baked_srules.ml"
python3 - "$X" <<'PY'
import re, sys
x = sys.argv[1]
for mod, name, lit in [('JSON', 'json_srules', 'json'), ('CSV', 'csv_srules', 'csv'), ('XML', 'xml_srules', 'xml')]:
    p = f'{x}/{mod}.ml'
    s = open(p).read()
    m = re.search(r'^let ' + name + r' =\n(?:.+\n)*?(?=\n)', s, re.M)
    if not m:
        sys.exit(f'ocaml_bake: no definition of {name} in {p}')
    s = s[:m.start()] + f'let {name} =\n  Marshal.from_string Baked_srules.{lit} 0\n' + s[m.end():]
    open(p, 'w').write(s)
PY
ls -l "$X/baked_srules.ml" | awk '{print "ocaml_bake: baked_srules.ml", $5, "bytes"}'
