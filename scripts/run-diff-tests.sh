#!/bin/bash
# Differential testing: Crane C++ vs Rocq OCaml extraction
# Compiles both sides, runs both, diffs output.
set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
BASICS="$PROJECT_ROOT/tests/basics"

PASS=0
FAIL=0
ERRORS=""

# Build all .vo files (triggers both Crane and OCaml extraction)
echo "=== Building with dune ==="
cd "$PROJECT_ROOT"
eval $(opam env --switch=default --set-switch)
dune build tests/basics 2>&1

# Second pass: Crane writes .cpp/.h to source tree during coqc;
# dune's (source_tree .) snapshots before build, so generated files
# aren't visible until the second build.
dune build tests/basics 2>&1

run_diff_test() {
    local name="$1"
    local subdir="$2"
    local ocaml_module="$3"  # extracted .ml basename (without .ml)
    local cpp_exe="$subdir/${name}.d.exe"
    local build_dir="_build/default/tests/basics"

    echo ""
    echo "--- $name ---"

    # Build C++ diff harness
    if [ ! -f "$build_dir/$subdir/${name}.d.exe" ]; then
        echo "  Building C++ diff harness..."
        dune build "tests/basics/$subdir/${name}.d.exe" 2>&1
    fi

    # Find the extracted OCaml .ml file
    # OCaml Extraction writes to the theory root (tests/basics/), not the subdir
    local ml_file="$BASICS/${ocaml_module}.ml"
    local mli_file="$BASICS/${ocaml_module}.mli"
    local ml_harness="$BASICS/$subdir/${name}.d.ml"

    if [ ! -f "$ml_file" ]; then
        echo "  ERROR: extracted $ml_file not found"
        FAIL=$((FAIL + 1))
        ERRORS="$ERRORS\n  $name: missing $ml_file"
        return
    fi

    if [ ! -f "$ml_harness" ]; then
        echo "  ERROR: OCaml harness $ml_harness not found"
        FAIL=$((FAIL + 1))
        ERRORS="$ERRORS\n  $name: missing $ml_harness"
        return
    fi

    # Compile OCaml side
    echo "  Compiling OCaml..."
    local ocaml_build_dir="$BASICS/$subdir/_ocaml_diff"
    mkdir -p "$ocaml_build_dir"

    # Compile .mli -> .cmi if it exists
    if [ -f "$mli_file" ]; then
        ocamlfind ocamlopt -package stdlib-shims -I "$ocaml_build_dir" \
            -c "$mli_file" -o "$ocaml_build_dir/${ocaml_module}.cmi" 2>&1
    fi

    # Compile extracted .ml -> .cmx
    ocamlfind ocamlopt -package stdlib-shims -I "$ocaml_build_dir" \
        -c "$ml_file" -o "$ocaml_build_dir/${ocaml_module}.cmx" 2>&1

    # Compile harness .ml -> .cmx
    ocamlfind ocamlopt -package stdlib-shims -I "$ocaml_build_dir" \
        -c "$ml_harness" -o "$ocaml_build_dir/${name}.d.cmx" 2>&1

    # Link
    ocamlfind ocamlopt -package stdlib-shims -linkpkg \
        "$ocaml_build_dir/${ocaml_module}.cmx" \
        "$ocaml_build_dir/${name}.d.cmx" \
        -o "$ocaml_build_dir/${name}.d.ocaml" 2>&1

    # Run both
    echo "  Running C++..."
    local cpp_out
    cpp_out=$("$build_dir/$subdir/${name}.d.exe" 2>&1)

    echo "  Running OCaml..."
    local ml_out
    ml_out=$("$ocaml_build_dir/${name}.d.ocaml" 2>&1)

    # Diff
    if [ "$cpp_out" = "$ml_out" ]; then
        echo "  PASS"
        PASS=$((PASS + 1))
    else
        echo "  FAIL: output differs"
        echo "  C++:"
        echo "$cpp_out" | sed 's/^/    /'
        echo "  OCaml:"
        echo "$ml_out" | sed 's/^/    /'
        FAIL=$((FAIL + 1))
        ERRORS="$ERRORS\n  $name: output mismatch"
    fi
}

# Run differential tests
# Args: test_name subdir ocaml_module_basename
run_diff_test "ack" "ack" "ack_ocaml"
run_diff_test "mutual_mod" "mutual_mod" "mutual_mod_ocaml"
run_diff_test "module" "module" "module_ocaml"

# Summary
echo ""
echo "=== Differential Test Results ==="
echo "  Passed: $PASS"
echo "  Failed: $FAIL"
if [ $FAIL -gt 0 ]; then
    echo -e "  Errors:$ERRORS"
    exit 1
fi
