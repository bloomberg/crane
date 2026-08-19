# parse-a-lot benchmark harness

This directory benchmarks the verified [`Crane.Libraries.ParseALot`](../../theories/Libraries/ParseALot)
lexer/parser (Verbatim++ lexer + CoStar++ parser) against native baselines, on
three grammars — **JSON, CSV, XML** — across three back ends:

| back end    | source                                            | notes                          |
|-------------|---------------------------------------------------|--------------------------------|
| OCaml       | plain Coq→OCaml extraction (`Extraction.v`)       | the verified pipeline, baseline|
| Crane / C++ | Coq→C++ extraction via the Crane plugin (`CraneExtraction.v`) | the pipeline crane emits |
| reference   | simdjson (JSON), libxml2 (XML)                     | third-party, JSON/XML only     |

It is the harness used to establish the "beats OCaml on large inputs" numbers
recorded in the crane docs.

## This sub-project is excluded from the crane build

It has its own `dune-project`, `_CoqProject`, and `Makefile`, and it depends on
packages that are **not** rocq-crane dependencies (`yojson`, `immer`, `simdjson`,
`libxml2`, `hyperfine`) plus a benchmark corpus that is not distributed here. The
parent `../dune` marks this directory `data_only_dirs`, so a plain `dune build` /
`dune build @all` / `make test` in crane never descends into it. Build it
standalone, from inside this directory, as described below.

## Corpus (git submodules + `make stage-data`)

Each format's raw data is a pinned **git submodule** under `corpus-src/`, one per
format (see [`corpus/PROVENANCE.toml`](corpus/PROVENANCE.toml)):

| format | submodule (`corpus-src/…`) | upstream | license |
|--------|----------------------------|----------|---------|
| JSON | `json` | [`unitedstates/congress-legislators`](https://github.com/unitedstates/congress-legislators) | CC0-1.0 |
| CSV  | `csv`  | [`tinytoolkit-org/csv-datasets`](https://github.com/tinytoolkit-org/csv-datasets) | CC0-1.0 |
| XML  | `xml`  | [`oanc/masc`](https://github.com/oanc/masc) (MASC GrAF corpus) | ANC "free" terms (non-SPDX) |

`bench.ml` reads a **flat** directory and parses **every** file in it, but the
submodules contain files the grammars don't accept (non-ASCII, semicolon/BOM CSV,
XML with text nodes, and — for JSON — YAML rather than JSON). So a submodule is
never pointed at directly: `make stage-data` curates each source into

```
$(DATA)/JSON/Instances   $(DATA)/JSON/SmallInstances
$(DATA)/CSV/Instances    $(DATA)/CSV/SmallInstances
$(DATA)/XML/Instances    $(DATA)/XML/SmallInstances
```

keeping only files the grammar accepts — the *authoritative* filter is a built
runner (a candidate is kept iff it parses to `unique`/`ambig`). Small files use
the fast OCaml runner; the ladders deliberately extend into the ~1.5 MB range to
**showcase the C++ back end parsing inputs the OCaml one cannot** (OCaml parses
by deep non-tail recursion and stack-overflows above a few hundred KB — macOS
caps the main-thread stack below that point, so it can't be raised), so above
~400 KB the `run_<fmt>_crane.exe` runner is the acceptance authority. Because
OCaml overflows there, `make bench` cross-checks OCaml-vs-C++ only on the
≤~400 KB overlap; the larger rungs are a C++ robustness showcase — run
`run_<fmt>_crane.exe` on them directly. The staged `data/` tree is gitignored and
regenerated on demand. To populate it:

```sh
git submodule update --init          # fetch corpus-src/{json,csv,xml}
make stage-data                      # builds the runners, then curates -> ./data
# or per format: make stage-json / stage-csv / stage-xml
# override the target root with DATA=/path (also honored by the bench-* targets)
```

Grammar/dialect constraints the staging enforces (see
[`../../theories/Libraries/ParseALot/Examples`](../../theories/Libraries/ParseALot/Examples)):

- **all** — 7-bit ASCII only (the lexer's char classes cover ASCII; no BOM).
- **CSV** — **RFC 4180**, comma-delimited only: quoted fields (`"…"`) may contain
  commas, CR/LF, and doubled-quote (`""`) escapes; records are separated by LF or
  CRLF; empty fields are allowed; a trailing newline yields one final empty
  record. Semicolon/tab dialects and the `broken/` fixtures are dropped.
- **XML** — **element-only**: nested tags + attributes, no text nodes, comments,
  CDATA, DOCTYPE, or entity references (matches the GrAF/XCES stand-off shape).
- **JSON** — the congress-legislators dataset, sliced into size-graded prefixes.

You can still point `DATA` at any other corpus with this layout. Until data is
staged, everything up to and including `make bench-build` still works; only the
`bench-*` targets need the data.

## Prerequisites

1. **rocq-crane installed** (provides the Crane plugin and the
   `Crane.Libraries.ParseALot.*` theory on `COQPATH`):
   ```sh
   make -C ../.. install       # i.e. dune build @install && dune install
   ```
2. **opam**: `yojson`, `unix` (OCaml runners); `coq-color` (already a rocq-crane
   dependency).
3. **immer** headers, default `$(HOME)/cpp/immer` — override with `IMMER=/path`.
4. **simdjson** / **libxml2** for the reference baselines.
5. **hyperfine** on `PATH` for wall-clock measurement.

## Usage

```sh
make coq-extract     # Coq -> OCaml into ./extracted
make ocaml-build     # build the OCaml runners (dune)
make crane-build     # Coq -> C++ into ./crane_extracted, then compile the C++ runners
make bench-build     # everything above + the simdjson/libxml2 reference runners
make closure-check   # report which interned-DFA rules are closed (no corpus needed)

# with a corpus in ./data (or DATA=/path/to/corpus):
make bench                       # all grammars, large + small
make bench-json BENCH_FLAGS='--warmup 3 --runs 10'
```

Results are written as `*_results.json` next to the Makefile.

## Licensing

The harness sources here (`.ml`, `.cpp`, `.h`) and the extraction drivers
(`.v`) are BSD-3-Clause, consistent with the library they exercise; see
[`../../theories/Libraries/ParseALot/LICENSE`](../../theories/Libraries/ParseALot/LICENSE)
and [`PROVENANCE.md`](../../theories/Libraries/ParseALot/PROVENANCE.md). Each file
carries an `SPDX-License-Identifier` header. The surrounding crane repository is
LGPL-2.1; simdjson, libxml2, immer, and yojson are third-party and separately
licensed.
