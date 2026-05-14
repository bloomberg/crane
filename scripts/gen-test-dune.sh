#!/bin/bash
# Generate (subdir ...) stanzas for dune test infrastructure
# Usage: ./scripts/gen-test-dune.sh [basics|monadic|regression|wip]

category=${1:-basics}

for dir in tests/$category/*/; do
    name=$(basename "$dir")
    # Find all .v files
    vfiles=($(ls "$dir"*.v 2>/dev/null | sort))
    vfile=$(basename "${vfiles[0]}" 2>/dev/null)
    vofile="${vfile%.v}.vo"

    if [ -f "$dir$name.t.cpp" ] && [ -n "$vfile" ]; then
        # Check if this is a BDE test (name ends with _bde) or GMP test (name ends with _gmp)
        if [[ "$name" == *_bde ]]; then
            compile_script="compile-bde.sh"
        elif [[ "$name" == *_gmp ]]; then
            compile_script="compile-gmp.sh"
        else
            compile_script="compile-std.sh"
        fi
        # Separate Extraction generates .cpp named after the .v file (PascalCase),
        # not the directory name (snake_case).
        # Check ALL .v files for Separate Extraction.
        sep_ext_vfiles=()
        for vf in "${vfiles[@]}"; do
            if grep -q "Crane Separate Extraction" "$vf" 2>/dev/null; then
                sep_ext_vfiles+=("$vf")
            fi
        done
        if [ ${#sep_ext_vfiles[@]} -gt 0 ]; then
            # Build deps from all separate-extraction .vo files
            vodeps=""
            cppsrcs=""
            for vf in "${sep_ext_vfiles[@]}"; do
                base=$(basename "${vf%.v}")
                vodeps="$vodeps ${base}.vo"
                cppsrcs="$cppsrcs ${base}.cpp"
            done
            vodeps=$(echo $vodeps)
            cppsrcs=$(echo $cppsrcs)
        else
            vodeps="$vofile"
            cppsrcs="$name.cpp"
        fi
            cat << EOF
(subdir $name
 (rule
  (targets $name.t.exe)
  (deps $vodeps $name.t.cpp (source_tree .))
  (action
   (run %{project_root}/scripts/$compile_script %{project_root} $name.t.exe $cppsrcs $name.t.cpp)))
 (rule
  (alias runtest)
  (deps $name.t.exe)
  (action (run ./$name.t.exe))))

EOF
    fi
done
