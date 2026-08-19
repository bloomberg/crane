#!/usr/bin/env python3
# SPDX-License-Identifier: BSD-3-Clause
"""Curate the corpus submodules into a flat, parser-acceptable benchmark corpus.

`bench.ml` reads a *flat* directory (`Sys.readdir`, non-recursive) and parses
*every* file in it, cross-checking the OCaml and Crane back ends. The upstream
corpus submodules under ``corpus-src/`` cannot be pointed at directly: they hold
non-ASCII files, wrong-dialect CSV (semicolon/BOM), XML with text nodes/comments,
and (for JSON) YAML rather than JSON. This script curates each source into

    data/{JSON,CSV,XML}/{Instances,SmallInstances}

keeping only files the grammar actually accepts. The *authoritative* acceptance
test is a built runner: a candidate is kept iff the runner parses it to a full
result (``parse_result`` = ``unique`` or ``ambig`` -- a parse *reject* still
exits 0, so the exit code alone is not enough). Which runner is authoritative
depends on size: small files use the fast OCaml runner
(``_build/default/run_<fmt>.exe``), but the ladders deliberately extend past the
point where the OCaml runner stack-overflows (~a few hundred KB, up to ~1.5 MB)
to showcase the C++ (Crane) back end handling inputs OCaml cannot -- so above
``OCAML_SAFE_BYTES`` the Crane runner (``run_<fmt>_crane.exe``) is the acceptance
authority. A cheap prefilter (ASCII, dialect, element-only) trims the set before
we spawn runners. Run ``make stage-data`` (which builds both back ends first)
rather than invoking this directly.

Grammar constraints enforced (see theories/Libraries/ParseALot/Examples):
  * all  -- 7-bit ASCII only (the lexer alphabet's char classes cover ASCII);
            no UTF-8/UTF-16 BOM.
  * CSV  -- RFC 4180, comma-delimited only (reject ';'/tab dialects, broken/).
  * XML  -- element-only: no text nodes, comments, CDATA, DOCTYPE, entity refs.
  * JSON -- congress-legislators ships YAML; convert to a JSON array, drop
            non-ASCII members, emit increasing-length prefixes as a size ladder.
"""

import argparse
import json
import os
import re
import shutil
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
CORPUS = os.path.join(HERE, "corpus-src")
DATA = os.environ.get("DATA", os.path.join(HERE, "data"))
RUNNER = {
    "json": os.path.join(HERE, "_build", "default", "run_json.exe"),
    "csv": os.path.join(HERE, "_build", "default", "run_csv.exe"),
    "xml": os.path.join(HERE, "_build", "default", "run_xml.exe"),
}
# The C++ (Crane) runners parse via an explicit stack and keep going into the
# multi-MB range where the OCaml runners stack-overflow, so above OCAML_SAFE_BYTES
# they are the only back end that can validate a candidate (see `accepts`).
CRANE_RUNNER = {
    "json": os.path.join(HERE, "_build", "default", "run_json_crane.exe"),
    "csv": os.path.join(HERE, "_build", "default", "run_csv_crane.exe"),
    "xml": os.path.join(HERE, "_build", "default", "run_xml_crane.exe"),
}

# Rough targets, matching the upstream corpus shape (~100 regular + ~10 small).
MAX_INSTANCES = 100
SMALL_COUNT = 10
# Size ceilings for the ladders. The point of the large rungs is to *showcase the
# C++ back end handling inputs the OCaml one cannot*: OCaml parses via deep
# non-tail recursion and stack-overflows above a few hundred KB (macOS caps the
# main-thread stack below OCaml's overflow point, so raising `ulimit -s` does not
# help), while the Crane C++ runner keeps going into the MB range. We cap around
# 1.5 MB -- comfortably past OCaml's limit yet keeping the slow C++ parse
# (~20s/MB) tolerable for one-shot runs. Above the cap the parses get long enough
# that they stop being useful benchmark rungs.
JSON_MAX_BYTES = 1_500_000
XML_MAX_BYTES = 1_500_000
CSV_MAX_BYTES = 1_500_000
# Below this size the OCaml runner is a fast, equivalent acceptance proxy (OCaml
# and Crane agree on parse_nodes for every file both accept); at/above it OCaml
# risks stack overflow, so `accepts` switches to the Crane runner. Measured safe
# points: XML fine at 400KB / over ~790KB; CSV fine at 500KB / over ~700KB.
OCAML_SAFE_BYTES = 400_000
ACCEPT_TIMEOUT = 240             # seconds per runner invocation (C++ ~20s/MB)


# --------------------------------------------------------------------------
# helpers
# --------------------------------------------------------------------------
def die(msg):
    print(f"stage_data: error: {msg}", file=sys.stderr)
    sys.exit(1)


def is_ascii_bytes(b: bytes) -> bool:
    """True iff pure 7-bit ASCII and no UTF BOM."""
    if b.startswith(b"\xef\xbb\xbf") or b.startswith(b"\xff\xfe") or b.startswith(b"\xfe\xff"):
        return False
    return all(c < 128 for c in b)


def accepts(fmt: str, path: str) -> bool:
    """Authoritative filter: the runner *parses* the file to a full result.

    Which runner is authoritative depends on size. Below OCAML_SAFE_BYTES the
    OCaml runner is a fast, equivalent proxy (OCaml and Crane agree on
    parse_nodes for every file both accept); at/above it the OCaml runner
    stack-overflows, so we probe with the Crane C++ runner, which is the back end
    the large rungs exist to showcase. Either runner only exits non-zero on a lex
    failure or exception; a parse *reject* still prints a metadata line and exits
    0, so success is signalled by the ``parse_result`` field being ``unique`` or
    ``ambig`` (see Parser.show_result), not by the exit code.
    """
    runner = RUNNER[fmt] if os.path.getsize(path) <= OCAML_SAFE_BYTES \
        else CRANE_RUNNER[fmt]
    try:
        r = subprocess.run([runner, path], capture_output=True,
                           timeout=ACCEPT_TIMEOUT)
    except subprocess.TimeoutExpired:
        return False
    if r.returncode != 0:
        return False
    out = r.stdout.decode("utf-8", "replace")
    return ('"parse_result":"unique"' in out
            or '"parse_result":"ambig"' in out)


def ensure_runner(fmt: str):
    if not os.path.exists(RUNNER[fmt]):
        die(f"missing runner {RUNNER[fmt]} -- run `make ocaml-build` first "
            "(or use `make stage-data`).")
    if not os.path.exists(CRANE_RUNNER[fmt]):
        die(f"missing runner {CRANE_RUNNER[fmt]} -- run `make crane-build` first "
            "(the large rungs are acceptance-checked with the C++ runner).")


def reset_dir(fmt: str):
    for sub in ("Instances", "SmallInstances"):
        d = os.path.join(DATA, fmt.upper(), sub)
        if os.path.isdir(d):
            shutil.rmtree(d)
        os.makedirs(d, exist_ok=True)


def bucket_and_report(fmt: str, staged):
    """staged: list of (size, name, bytes). Writes Instances + SmallInstances."""
    staged.sort(key=lambda t: t[0])              # by size ascending
    inst = os.path.join(DATA, fmt.upper(), "Instances")
    small = os.path.join(DATA, fmt.upper(), "SmallInstances")
    for seq, (_, name, data) in enumerate(staged):
        with open(os.path.join(inst, f"{seq:03d}_{name}"), "wb") as f:
            f.write(data)
    for seq, (_, name, data) in enumerate(staged[:SMALL_COUNT]):
        with open(os.path.join(small, f"{seq:03d}_{name}"), "wb") as f:
            f.write(data)
    if staged:
        print(f"  [{fmt}] staged {len(staged)} Instances "
              f"({staged[0][0]}..{staged[-1][0]} bytes), "
              f"{min(SMALL_COUNT, len(staged))} SmallInstances")
    else:
        print(f"  [{fmt}] WARNING: 0 files staged")


def walk_files(root, suffix):
    for dirpath, _, names in os.walk(root):
        for n in names:
            if n.endswith(suffix):
                yield os.path.join(dirpath, n)


def geometric_targets(lo, hi, n):
    """n geometrically-spaced size targets in [lo, hi] (ascending, lo,hi>=1)."""
    lo = max(1, lo)
    hi = max(lo, hi)
    if n <= 1 or lo == hi:
        return [hi]
    ratio = (hi / lo) ** (1.0 / (n - 1))
    return [int(round(lo * ratio ** i)) for i in range(n)]


def spread_by_size(fmt, candidates, cap, want, probe):
    """Pick a geometric size ladder of accepted files from `candidates`.

    candidates: list of (size, name, bytes) with any size. Walks `want`
    geometric size targets from the smallest to the largest capped candidate,
    and for each target takes the nearest not-yet-used file that the runner
    accepts, scanning outward so a reject/overflow near the target doesn't leave
    a hole. `probe(bytes)` writes the candidate to a temp path and returns it so
    accepts() can run the runner. Returns up to `want` (size, name, bytes)
    tuples spread across the size range.
    """
    pool = sorted((t for t in candidates if t[0] <= cap), key=lambda t: t[0])
    if not pool:
        return []
    sizes = [t[0] for t in pool]
    used = set()
    picked = []
    import bisect
    for target in geometric_targets(sizes[0], sizes[-1], want):
        j = bisect.bisect_left(sizes, target)
        # scan outward from the target position for the nearest accepted, unused file
        order = sorted(range(len(pool)), key=lambda i: (abs(sizes[i] - target), i))
        for i in order:
            if i in used:
                continue
            size, name, data = pool[i]
            tmp = probe(data)
            ok = accepts(fmt, tmp)
            os.remove(tmp)
            if ok:
                used.add(i)
                picked.append((size, name, data))
                break
            used.add(i)  # a reject/overflow: don't retry it for later targets
    picked.sort(key=lambda t: t[0])
    return picked


# --------------------------------------------------------------------------
# JSON: congress-legislators YAML -> JSON array -> size-ladder prefixes
# --------------------------------------------------------------------------
def yaml_to_json_array(yaml_path):
    """Convert a YAML sequence to a Python list, trying yq then ruby then pyyaml."""
    # yq v4 (mikefarah): emit compact JSON.
    if shutil.which("yq"):
        try:
            out = subprocess.run(["yq", "-o=json", "-I=0", ".", yaml_path],
                                capture_output=True, timeout=300, check=True).stdout
            return json.loads(out)
        except Exception:
            pass
    if shutil.which("ruby"):
        try:
            out = subprocess.run(
                ["ruby", "-ryaml", "-rjson", "-e",
                 "puts JSON.generate(YAML.load_file(ARGV[0]))", yaml_path],
                capture_output=True, timeout=300, check=True).stdout
            return json.loads(out)
        except Exception:
            pass
    try:
        import yaml  # type: ignore
        with open(yaml_path) as f:
            return yaml.safe_load(f)
    except Exception:
        die("need `yq` (v4), `ruby`, or python `pyyaml` to convert legislators YAML")


def stage_json():
    ensure_runner("json")
    reset_dir("json")
    src = os.path.join(CORPUS, "json", "legislators-historical.yaml")
    if not os.path.exists(src):
        die(f"missing {src} -- run `git submodule update --init`")
    arr = yaml_to_json_array(src)
    if not isinstance(arr, list):
        die("legislators YAML did not parse to a JSON array")
    # keep only members whose JSON serialization is pure ASCII
    ascii_members = [m for m in arr
                     if json.dumps(m).encode() == json.dumps(m).encode("ascii", "ignore")]
    print(f"  [json] {len(ascii_members)}/{len(arr)} members are ASCII-clean")

    # geometric-ish ladder of prefix lengths, capped by byte size
    ladder, k = [], 1
    while k <= len(ascii_members):
        ladder.append(k)
        k *= 2
    if len(ascii_members) not in ladder:
        ladder.append(len(ascii_members))

    staged, seen_bytes = [], set()
    for k in ladder:
        blob = json.dumps(ascii_members[:k], indent=2).encode()
        if len(blob) > JSON_MAX_BYTES:
            break
        if len(blob) in seen_bytes:
            continue
        seen_bytes.add(len(blob))
        name = f"legislators_{k:04d}.json"
        tmp = os.path.join(DATA, "JSON", "Instances", name)
        with open(tmp, "wb") as f:
            f.write(blob)
        ok = accepts("json", tmp)
        os.remove(tmp)
        if ok:
            staged.append((len(blob), name, blob))
    bucket_and_report("json", staged)


# --------------------------------------------------------------------------
# CSV: csv-datasets -> comma+ASCII+RFC4180 files, plus row-slices of the largest
# --------------------------------------------------------------------------
def csv_is_comma_delimited(b: bytes) -> bool:
    line = b.split(b"\n", 1)[0]
    commas, semis, tabs = line.count(b","), line.count(b";"), line.count(b"\t")
    return commas >= 1 and commas >= semis and commas >= tabs


def stage_csv():
    ensure_runner("csv")
    reset_dir("csv")
    root = os.path.join(CORPUS, "csv")
    if not os.path.isdir(root):
        die(f"missing {root} -- run `git submodule update --init`")
    # skip deliberately-malformed and generator dirs
    skip = {os.path.join(root, "broken"), os.path.join(root, "generators")}

    candidates = []
    for p in walk_files(root, ".csv"):
        if any(p.startswith(s + os.sep) for s in skip):
            continue
        b = open(p, "rb").read()
        if not is_ascii_bytes(b) or not csv_is_comma_delimited(b):
            continue
        candidates.append((p, b))

    staged, biggest = [], None
    for p, b in candidates:
        if biggest is None or len(b) > biggest[0]:
            biggest = (len(b), b)      # largest comma+ASCII file, accepted or not
        if len(b) > CSV_MAX_BYTES:
            continue                   # over the ceiling: skip the (slow) probe;
                                       # `biggest` still feeds the slice ladder below
        tmp = os.path.join(DATA, "CSV", "Instances", "._probe.csv")
        with open(tmp, "wb") as f:
            f.write(b)
        ok = accepts("csv", tmp)
        os.remove(tmp)
        if ok:
            staged.append((len(b), os.path.basename(p), b))

    # Fill a size ladder with line-boundary prefixes of the largest comma+ASCII
    # file, up to the safe cap. The biggest real files are multi-MB and overflow
    # the runner, so slicing them (not just the largest *accepted* file) is what
    # lets the ladder reach the hundreds-of-KB range.
    if biggest and biggest[0] > 20_000:
        lines = biggest[1].split(b"\n")
        seen = {s for s, _, _ in staged}
        for target in geometric_targets(20_000, min(biggest[0], CSV_MAX_BYTES), 12):
            acc = bytearray()
            for ln in lines:
                acc += ln + b"\n"
                if len(acc) >= target:
                    break
            blob = bytes(acc)
            if len(blob) > CSV_MAX_BYTES or len(blob) in seen:
                continue
            tmp = os.path.join(DATA, "CSV", "Instances", "._probe.csv")
            with open(tmp, "wb") as f:
                f.write(blob)
            ok = accepts("csv", tmp)
            os.remove(tmp)
            if ok:
                seen.add(len(blob))
                staged.append((len(blob), f"slice_{len(blob)}.csv", blob))

    # de-dup by (size,name) and cap
    staged.sort(key=lambda t: t[0])
    staged = staged[:MAX_INSTANCES]
    bucket_and_report("csv", staged)


# --------------------------------------------------------------------------
# XML: oanc/masc GrAF -> element-only + ASCII files (acceptance-filtered)
# --------------------------------------------------------------------------
_DECL = re.compile(rb"<\?xml.*?\?>", re.S)
_TEXTNODE = re.compile(rb">([^<]*)<")


def xml_is_element_only(b: bytes) -> bool:
    if b"<!--" in b or b"<![CDATA[" in b or b"<!DOCTYPE" in b:
        return False
    if re.search(rb"&[A-Za-z#][A-Za-z0-9]*;", b):     # entity references
        return False
    body = _DECL.sub(b"", b)
    for seg in _TEXTNODE.findall(body):               # text between > and <
        if seg.strip():
            return False
    return True


def stage_xml():
    ensure_runner("xml")
    reset_dir("xml")
    root = os.path.join(CORPUS, "xml")
    if not os.path.isdir(root):
        die(f"missing {root} -- run `git submodule update --init`")

    prefiltered = []
    for p in walk_files(root, ".xml"):
        b = open(p, "rb").read()
        if not is_ascii_bytes(b) or not xml_is_element_only(b):
            continue
        prefiltered.append((len(b), os.path.basename(p), b))
    n_over_cap = sum(1 for s, _, _ in prefiltered if s > XML_MAX_BYTES)
    print(f"  [xml] {len(prefiltered)} files pass the element-only/ASCII prefilter "
          f"({n_over_cap} over the {XML_MAX_BYTES}-byte cap)")

    # Pick a geometric size ladder of accepted files (rather than the 100
    # smallest): the grammar accepts nested XML up to the cap, but the corpus is
    # dominated by tiny GrAF layer files, so a naive smallest-first cap clusters
    # everything at a few hundred bytes.
    def probe(data):
        tmp = os.path.join(DATA, "XML", "Instances", "._probe.xml")
        with open(tmp, "wb") as f:
            f.write(data)
        return tmp
    staged = spread_by_size("xml", prefiltered, XML_MAX_BYTES, MAX_INSTANCES, probe)
    bucket_and_report("xml", staged)


# --------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("format", nargs="?", default="all",
                    choices=["all", "json", "csv", "xml"])
    args = ap.parse_args()
    print(f"stage_data: DATA={DATA}")
    if args.format in ("all", "json"):
        stage_json()
    if args.format in ("all", "csv"):
        stage_csv()
    if args.format in ("all", "xml"):
        stage_xml()


if __name__ == "__main__":
    main()
