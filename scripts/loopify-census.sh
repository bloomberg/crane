#!/usr/bin/env bash
# Check the recursion plan against Loopify on every function in the corpus.
#
# Loopify is opt-in, so an ordinary test run checks the recursion plan only
# against the few functions that ask for it.  This extracts the basics,
# monadic and regression tests again with Loopify on everywhere
# (CRANE_LOOPIFY_CENSUS), records what the IR checks report instead of
# failing on it, and compares the result with tests/loopify-census.golden,
# so the set of known disagreements can only change deliberately.
#
#   scripts/loopify-census.sh                    # check against the baseline
#   scripts/loopify-census.sh --accept           # rewrite the baseline
#   scripts/loopify-census.sh --compile          # compile and run it too
#   scripts/loopify-census.sh --compile --accept
#
# The plain census writes no generated files: it checks what the plan and
# the lowering agree on, which says nothing about whether the lowered code
# compiles.  With --compile the extraction writes its files (write:<log>),
# under _build/compile-census/tests, and every test is compiled from them
# with its own .t.cpp, as its rule in the folder's dune file compiles it,
# and run; the tests that do not build, compile, or pass are compared with
# tests/loopify-compile-census.golden.  It takes much longer and is not
# part of `make test`.
#
# Each census builds in a build directory of its own: its .vo files say
# nothing about the committed output, which an ordinary build must not take
# as up to date.  The variable is not one dune tracks, so the cache is off
# and the .vo files are removed first; a test that does not build is
# reported as failing.

set -uo pipefail

cd "$(dirname "$0")/.."

compile=false
accept=false
for arg in "$@"; do
  case $arg in
    --compile) compile=true ;;
    --accept) accept=true ;;
    *)
      echo "usage: $0 [--compile] [--accept]" >&2
      exit 2
      ;;
  esac
done

# dune takes a build directory inside _build only as an absolute path.
if $compile; then
  GOLDEN=tests/loopify-compile-census.golden
  ROOT=$PWD/_build/compile-census
  # The tests write their files to ../../tests/<folder> of the build
  # context, which this puts at $ROOT/tests.
  BUILD=$ROOT/b
  OUTPUT=$ROOT/tests
else
  GOLDEN=tests/loopify-census.golden
  BUILD=$PWD/_build/census
fi
# Nor does it make the directory that build directory is in.
mkdir -p "$(dirname "$BUILD")"
LOG=$(mktemp)
OUT=$(mktemp)
ACTUAL=$(mktemp)
trap 'rm -f "$LOG" "$OUT" "$ACTUAL"' EXIT

sources=$(ls tests/basics/*/*.v tests/monadic/*/*.v tests/regression/*/*.v)
targets=$(echo "$sources" | sed 's/\.v$/.vo/')

find "$BUILD/default/tests" -name '*.vo' -delete 2>/dev/null
if $compile; then
  rm -rf "$OUTPUT"
  mkdir -p "$ROOT"
  # Each test's sources sit where its files are written, as they do in the
  # tree: extraction reads the doc comments off the .v it finds there.
  for v in $sources; do
    mkdir -p "$ROOT/$(dirname "$v")"
    cp "$v" "$ROOT/$v"
  done
  CENSUS=write:$LOG
else
  CENSUS=$LOG
fi

echo "Extracting the test corpus with Loopify on everywhere..." >&2
# The plugin is installed first, on its own: coqc loads it from the install
# directory, which dune's rules for the theories and the tests do not wait
# for in a build directory of its own.  A run that started one too early
# reports the plugin unavailable but still installs it, so the install is
# tried twice; a real failure fails both times.
if ! dune build --build-dir "$BUILD" @install > "$OUT" 2>&1 &&
  ! dune build --build-dir "$BUILD" @install > "$OUT" 2>&1; then
  cat "$OUT" >&2
  exit 1
fi
# shellcheck disable=SC2086
CRANE_LOOPIFY_CENSUS=$CENSUS dune build --build-dir "$BUILD" --cache=disabled \
  $targets > "$OUT" 2>&1

units=$(grep -c '^extracted: ' "$LOG")
if [ "$units" -eq 0 ]; then
  echo "loopify census: no unit was extracted; the census did not run" >&2
  exit 1
fi

unbuilt() {
  for v in $sources; do
    [ -f "$BUILD/default/${v%.v}.vo" ] || echo "does not build: $v"
  done
}

# compile_one FOLDER NAME SCRIPT EXE RUN SOURCES...: compile the test's
# extracted files with its .t.cpp, as its rule does, and run it if RUN is
# yes; prints the finding, if any.  The test directory's own files that the
# extraction did not write -- its .t.cpp, a header written by hand -- are
# copied in; a source the rule names is never taken from the committed
# output.
compile_one() {
  local folder=$1 name=$2 script=$3 exe=$4 run=$5
  shift 5
  local dir=$OUTPUT/$folder/$name src=tests/$folder/$name
  # A test that does not build is reported as such, and not compiled.
  compgen -G "$BUILD/default/$src/*.vo" > /dev/null || return 0
  for f in "$src"/*; do
    case $f in
      *.t.cpp) cp "$f" "$dir/" ;;
      *.v | *.cpp) ;;
      *) [ -e "$dir/$(basename "$f")" ] || cp "$f" "$dir/" ;;
    esac
  done
  if ! (cd "$dir" && "$OLDPWD/scripts/$script" "$OLDPWD" "$exe" "$@") > "$dir/compile.log" 2>&1; then
    echo "does not compile: $src"
    return 0
  fi
  [ "$run" = yes ] || return 0
  # No timeout(1) here: a watchdog kills a run that takes longer than 20 s.
  # The subshell's stderr is closed so that the shell's report of a killed
  # run does not pass for a finding.
  (
    cd "$dir" || exit 1
    "./$exe" < /dev/null > run.log 2>&1 &
    pid=$!
    (sleep 20 && kill -9 "$pid" 2> /dev/null) &
    watchdog=$!
    wait "$pid"
    status=$?
    kill "$watchdog" 2> /dev/null
    exit "$status"
  ) 2> /dev/null
  case $? in
    0) ;;
    137) echo "times out: $src" ;;
    *) echo "fails: $src" ;;
  esac
}

# The compile rule and run rule of every test, one line each, from the
# folders' dune files: FOLDER NAME SCRIPT EXE RUN SOURCES...  A test built
# against a library this machine may lack (compile-bde.sh) is left out.
compile_rules() {
  for folder in basics monadic regression; do
    awk -v folder="$folder" '
      /^\(subdir / { name = $2; script = ""; run = "no" }
      /\(run %\{project_root\}\/scripts\/compile-[a-z]+\.sh %\{project_root\}/ {
        script = $2; sub(/.*\/scripts\//, "", script)
        line = $0; sub(/^.*%\{project_root\} /, "", line); sub(/\)+$/, "", line)
        rule = line
      }
      /\(action \(run \.\/[^ ]*\.t\.exe\)\)/ { run = "yes" }
      /^$/ && name != "" && script != "" {
        if (script != "compile-bde.sh") print folder, name, script, run, rule
        name = ""; script = ""
      }
      END { if (name != "" && script != "" && script != "compile-bde.sh") print folder, name, script, run, rule }
    ' "tests/$folder/dune"
  done
}

if $compile; then
  echo "Compiling and running the extracted tests..." >&2
  export OUTPUT BUILD
  export -f compile_one
  rules=$(compile_rules)
  compiled=$(echo "$rules" | grep -c .)
  if [ "$compiled" -eq 0 ]; then
    echo "loopify census: no compile rule was found; the census did not run" >&2
    exit 1
  fi
  {
    unbuilt
    # FOLDER NAME SCRIPT RUN EXE SOURCES... -> compile_one's argument order.
    echo "$rules" | awk '{ t = $4; $4 = $5; $5 = t; print }' |
      xargs -P "$(sysctl -n hw.ncpu 2> /dev/null || nproc)" -L 1 bash -c 'compile_one "$@"' _
  } | sort -u > "$ACTUAL"
else
  {
    grep -v '^extracted: ' "$LOG"
    unbuilt
  } | sort -u > "$ACTUAL"
fi

if grep -q '^does not build: ' "$ACTUAL"; then
  grep -B1 -A8 '^Error' "$OUT" >&2
fi

if $accept; then
  cp "$ACTUAL" "$GOLDEN"
  echo "Wrote $(wc -l < "$GOLDEN" | tr -d ' ') findings to $GOLDEN" >&2
  exit 0
fi

if diff -u "$GOLDEN" "$ACTUAL"; then
  echo "loopify census unchanged: $(wc -l < "$ACTUAL" | tr -d ' ') findings in $units units" >&2
  exit 0
fi

cat >&2 << 'MSG'

loopify census changed.
  Lines starting '-' are findings that are now gone  -> run with --accept.
  Lines starting '+' are new findings                -> a regression.
MSG
exit 1
