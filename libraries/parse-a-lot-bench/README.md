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

## Corpus (not included)

The original parse-a-lot corpus is **not** redistributed with crane. Supply your
own and point `DATA` at it. The runners expect:

```
$(DATA)/JSON/Instances   $(DATA)/JSON/SmallInstances
$(DATA)/CSV/Instances    $(DATA)/CSV/SmallInstances
$(DATA)/XML/Instances    $(DATA)/XML/SmallInstances
```

The CSV grammar accepts **RFC 4180**: quoted fields (`"…"`) may contain commas,
CR/LF, and doubled-quote (`""`) escapes; records are separated by LF or CRLF;
empty fields are allowed. A trailing newline yields one final empty record.

Each `*Instances` directory holds one input file per benchmark case. Until a
corpus is present, everything up to and including `make bench-build` still works;
only the `bench-*` targets need the data.

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
