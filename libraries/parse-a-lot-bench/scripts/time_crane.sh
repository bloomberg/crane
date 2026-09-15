#!/bin/sh
# Wall-clock timing and peak RSS of the Crane-extracted parsers over the
# staged corpus.
#
# The comparative harness (bench.exe) needs the OCaml baseline runners, and
# `make ocaml-build` does not currently compile.  This measures just the Crane
# side, which is what a change to Crane's code generation moves.
#
# Files above MAXBYTES are skipped: the largest JSON rungs take minutes and
# tens of gigabytes each, so including them would make a before/after
# comparison impractical rather than more informative.
#
# Usage: scripts/time_crane.sh [runs] [corpus-dir]
#   MAXBYTES=n   per-file size cap (default 1000000)
set -eu

runs=${1:-3}
data=${2:-./data}
maxbytes=${MAXBYTES:-1000000}
exe=./_build/default

for lang in json csv xml; do
  case $lang in
    json) dir=JSON ;;
    csv)  dir=CSV ;;
    xml)  dir=XML ;;
  esac
  for set in SmallInstances Instances; do
    files=$(find "$data/$dir/$set" -type f -size -"$maxbytes"c | sort)
    [ -n "$files" ] || continue
    best=""
    peak=0
    i=0
    while [ "$i" -lt "$runs" ]; do
      i=$((i + 1))
      start=$(python3 -c 'import time; print(time.monotonic())')
      for f in $files; do
        rss=$(/usr/bin/time -l "$exe/run_${lang}_crane.exe" "$f" 2>&1 >/dev/null \
              | awk '/maximum resident set size/ { print $1 }')
        [ "$rss" -gt "$peak" ] && peak=$rss
      done
      end=$(python3 -c 'import time; print(time.monotonic())')
      best=$(python3 -c "b='$best'; t=$end-$start; print(f'{min(float(b),t) if b else t:.3f}')")
    done
    printf '%-4s %-14s %2s files  best-of-%s: %ss  peak RSS: %s MiB\n' \
      "$lang" "$set" "$(echo "$files" | wc -l | tr -d ' ')" "$runs" "$best" \
      "$(python3 -c "print(f'{$peak/1048576:.0f}')")"
  done
done
