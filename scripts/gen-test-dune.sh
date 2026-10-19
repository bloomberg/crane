#!/usr/bin/env bash
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
            # One `Crane Extraction "target"` command produces one target.cpp.
            # A directory may hold several -- a library unit and the unit that
            # consumes it -- and all of them have to be compiled and linked.
            # Commands wrapped in `Fail` (rejection regressions) produce
            # nothing, and the anchored pattern skips them.
            vodeps="$vofile"
            cppsrcs=""
            for vf in "${vfiles[@]}"; do
                targets=$(grep -hoE '^[[:space:]]*Crane([[:space:]]+[A-Za-z]+)*[[:space:]]+Extraction[[:space:]]+"[^"]+"' "$vf" 2>/dev/null \
                          | sed -E 's/.*"([^"]+)"$/\1/')
                for t in $targets; do
                    # A target written into a subdirectory is not part of this
                    # test's binary, and one with its own .t.cpp is a separate
                    # test sharing the directory -- linking it in would bring a
                    # second main().
                    case "$t" in */*) continue ;; esac
                    if [ "$t" != "$name" ] && [ -f "$dir$t.t.cpp" ]; then
                        continue
                    fi
                    case " $cppsrcs " in
                        *" $t.cpp "*) ;;
                        *) cppsrcs="$cppsrcs $t.cpp" ;;
                    esac
                done
            done
            cppsrcs=$(echo $cppsrcs)
        fi
        srcs=$(echo $cppsrcs $name.t.cpp)
            cat << EOF
(subdir $name
 (rule
  (targets $name.t.exe)
  (deps $vodeps $name.t.cpp (source_tree .))
  (action
   (run %{project_root}/scripts/$compile_script %{project_root} $name.t.exe $srcs)))
 (rule
  (alias runtest)
  (deps $name.t.exe)
  (action (run ./$name.t.exe))))

EOF
    fi
done
