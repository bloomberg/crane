#!/bin/bash
# Generate (subdir ...) stanzas for dune test infrastructure
# Usage: ./scripts/gen-test-dune.sh [basics|monadic|regression|wip]

category=${1:-basics}

for dir in tests/$category/*/; do
    name=$(basename "$dir")
    # Find the .v file (e.g., List.v)
    vfile=$(basename "$(ls "$dir"*.v 2>/dev/null | head -1)" 2>/dev/null)
    vofile="${vfile%.v}.vo"

    if [ -f "$dir$name.t.cpp" ] && [ -n "$vfile" ]; then
        # Check if this is a BDE test (name ends with _bde)
        if [[ "$name" == *_bde ]]; then
            cat << EOF
(subdir $name
 (rule
  (targets $name.t.exe)
  (deps $vofile $name.t.cpp (source_tree .))
  (action
   (run %{project_root}/scripts/compile-bde.sh %{project_root} $name.t.exe $name.cpp $name.t.cpp)))
 (rule
  (alias runtest)
  (deps $name.t.exe)
  (action (run ./$name.t.exe))))

EOF
        else
            cat << EOF
(subdir $name
 (rule
  (targets $name.t.exe)
  (deps $vofile $name.t.cpp (source_tree .))
  (action
   (run %{project_root}/scripts/compile-std.sh %{project_root} $name.t.exe $name.cpp $name.t.cpp)))
 (rule
  (alias runtest)
  (deps $name.t.exe)
  (action (run ./$name.t.exe))))

EOF
        fi
    fi
done
