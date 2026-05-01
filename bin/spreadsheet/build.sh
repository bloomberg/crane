#!/bin/bash
# Copyright 2026 Bloomberg Finance L.P.
# Distributed under the terms of the GNU LGPL v2.1 license.
#
# Build helper for the Crane spreadsheet demo.  Runs:
#   1. dune build src theories             — Crane plugin and theory deps
#   2. rocq compile (in _build/spreadsheet_gen) — extract Spreadsheet.{h,cpp}
#   3. cmake configure + build             — Dear ImGui front-end binary
#
# Run from the project root.  Usage:
#   ./bin/spreadsheet/build.sh

set -e
cd "$(git rev-parse --show-toplevel)"
ROOT="$(pwd)"
GEN="${ROOT}/_build/spreadsheet_gen"

echo "=== dune build (Crane plugin + theory deps) ==="
dune build src theories

echo
echo "=== rocq compile (extract Spreadsheet.{h,cpp}) ==="
rm -rf "${GEN}"
mkdir -p "${GEN}"
cp theories/Examples/Spreadsheet/Spreadsheet.v "${GEN}/Spreadsheet.v"
( cd "${GEN}" \
  && rocq compile -Q "${ROOT}/_build/default/theories" Crane Spreadsheet.v )
ls "${GEN}/Spreadsheet."{h,cpp}

echo
echo "=== cmake configure ==="
cmake -S bin/spreadsheet -B _build/spreadsheet -G "Unix Makefiles" \
  -DCRANE_GENERATED="${GEN}"

echo
echo "=== cmake build ==="
cmake --build _build/spreadsheet -j

echo
echo "=== done ==="
echo "Run with: ./_build/spreadsheet/spreadsheet"
