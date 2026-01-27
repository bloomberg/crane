#!/bin/bash
# Generate (subdir ...) stanzas for dune test infrastructure
# Usage: ./scripts/gen-test-dune.sh [basics|monadic]

category=${1:-basics}

for dir in tests/$category/*/; do
    name=$(basename "$dir")
    # Find the .v file (e.g., List.v)
    vfile=$(basename "$(ls "$dir"*.v 2>/dev/null | head -1)" 2>/dev/null)
    vofile="${vfile%.v}.vo"
    # Path from project root to test directory
    srcdir="tests/$category/$name"

    if [ -f "$dir$name.t.cpp" ] && [ -n "$vfile" ]; then
        cat << EOF
(subdir $name
 (rule
  (targets $name.t.exe)
  (deps $vofile $name.t.cpp (source_tree .))
  (action
   (run clang++ -std=c++23 -O2 -I %{project_root}/$srcdir %{project_root}/$srcdir/$name.cpp $name.t.cpp -o $name.t.exe)))
 (rule
  (alias runtest)
  (deps $name.t.exe)
  (action (run ./$name.t.exe))))

EOF
    fi
done
