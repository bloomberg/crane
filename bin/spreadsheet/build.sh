#!/bin/bash
# Copyright 2026 Bloomberg Finance L.P.
# Distributed under the terms of the GNU LGPL v2.1 license.
#
# Build helper for the Crane spreadsheet demo.  Runs:
#   1. dune build       — Crane plugin, theory deps, and the
#                         CraneSpreadsheet theory that extracts
#                         Spreadsheet.{h,cpp} into this directory.
#   2. cmake configure + build  — Dear ImGui front-end binary.
#
# Run from the project root.  Usage:
#   ./bin/spreadsheet/build.sh

set -e
cd "$(git rev-parse --show-toplevel)"

echo "=== dune build (plugin + theories + extraction) ==="
dune build src theories bin/spreadsheet

echo
echo "=== cmake configure ==="
cmake -S bin/spreadsheet -B _build/spreadsheet -G "Unix Makefiles"

echo
echo "=== cmake build ==="
cmake --build _build/spreadsheet -j

echo
echo "=== done ==="
echo "Run with: ./_build/spreadsheet/spreadsheet"
