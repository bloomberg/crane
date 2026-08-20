# =====================================================================
# parse-a-lot benchmark harness (standalone)
# =====================================================================
# This sub-project is NOT part of the rocq-crane dune build (see ../dune).
# It compares the verified ParseALot lexer/parser against native baselines
# across three grammars (JSON, CSV, XML), on three back ends:
#
#   * OCaml   -- plain Coq->OCaml extraction (Extraction.v -> ./extracted)
#   * Crane   -- Coq->C++ extraction via the Crane plugin (CraneExtraction.v
#                -> ./crane_extracted/Benchmarking)
#   * reference-- simdjson (JSON) and libxml2 (XML) as third-party baselines
#
# Prerequisites (none are rocq-crane build deps):
#   * rocq-crane installed:  make -C ../.. install   (gives the Crane plugin and
#     the Crane.Libraries.ParseALot.* theory on COQPATH)
#   * opam:  yojson, unix          (OCaml runners)
#   * coq-color                    (already a rocq-crane dep)
#   * immer headers at $(IMMER)    (default $(HOME)/cpp/immer) for the Crane C++
#   * simdjson / libxml2           (reference baselines only)
#   * hyperfine                    (wall-clock measurement in bench.ml)
#   * A benchmark corpus under $(DATA) -- NOT shipped with crane; see README.md.
# =====================================================================

.PHONY: all coq-extract crane-extract ocaml-build crane-build bench-build \
        closure-check clean \
        stage-data stage-json stage-csv stage-xml \
        bench bench-json bench-json-small bench-csv bench-csv-small \
        bench-xml bench-xml-small

all: bench-build

# ---------------------------------------------------------------
# Coq -> OCaml / Coq -> C++ extraction
# ---------------------------------------------------------------
CoqMakefile: _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

# Plain OCaml extraction into ./extracted
coq-extract: CoqMakefile
	$(MAKE) -f CoqMakefile Extraction.vo ClosureCheck.vo

# Crane C++ extraction into ./crane_extracted/Benchmarking
crane-extract: CoqMakefile
	$(MAKE) -f CoqMakefile CraneExtraction.vo

# ---------------------------------------------------------------
# OCaml runners (baseline)
# ---------------------------------------------------------------
ocaml-build: coq-extract
	dune build

# ---------------------------------------------------------------
# Crane C++ runners
# ---------------------------------------------------------------
CRANE_CXX       ?= c++
IMMER           ?= $(HOME)/cpp/immer
CRANE_CPP_DIR   := ../../theories/cpp
CRANE_EXT_DIR   := crane_extracted/Benchmarking
# IMMER_NO_THREAD_SAFETY=1: the runners are effectively single-threaded (one
# worker thread; main just joins), so switch immer to non-atomic refcounting.
CRANE_CXX_FLAGS := -O2 -std=c++23 -DIMMER_NO_THREAD_SAFETY=1 \
                   -iquote $(CRANE_EXT_DIR) -I$(CRANE_CPP_DIR) -I$(IMMER)
CRANE_SRCS      := $(wildcard $(CRANE_EXT_DIR)/*.cpp)

_build/default/run_%_crane.exe: run_%_crane.cpp $(CRANE_SRCS)
	@mkdir -p _build/default
	$(CRANE_CXX) $(CRANE_CXX_FLAGS) -o $@ $^

crane-build: crane-extract \
  _build/default/run_json_crane.exe \
  _build/default/run_csv_crane.exe \
  _build/default/run_xml_crane.exe

# ---------------------------------------------------------------
# Reference baselines: the fastest common third-party C++ parser per format.
#   * JSON -- simdjson   (run_json_ref.cpp)
#   * XML  -- pugixml     (run_xml_pugi.cpp);  libxml2 also kept (run_xml_ref.cpp)
#   * CSV  -- Vince La's csv-parser (run_csv_ref.cpp), a vendored single header
# simdjson/pugixml/libxml2 are brew/system deps; csv-parser's `csv.hpp` is
# fetched (checksum-verified) into vendor/ by the rule below -- not committed.
# ---------------------------------------------------------------
SIMDJSON_FLAGS := $(shell pkg-config --cflags --libs simdjson 2>/dev/null || echo "-I/opt/homebrew/include -lsimdjson")
XML2_FLAGS     := $(shell xml2-config --cflags --libs 2>/dev/null || pkg-config --cflags --libs libxml-2.0 2>/dev/null || echo "-I/usr/include/libxml2 -lxml2")
PUGIXML_FLAGS  := $(shell pkg-config --cflags --libs pugixml 2>/dev/null || echo "-I/opt/homebrew/include -L/opt/homebrew/lib -lpugixml")

# Vince La's csv-parser single header (MIT), pinned to release 5.3.0 by SHA-256.
CSVPARSER_VER    := 5.3.0
CSVPARSER_SHA256 := 330b0d8950ff8b566ae726c022e2396f1dcdee36cb9ad6f6c1badc8febbf4319
CSVPARSER_HDR    := vendor/csv-parser/csv.hpp

$(CSVPARSER_HDR):
	@mkdir -p $(dir $@)
	curl -fsSL -o $@ https://github.com/vincentlaucsb/csv-parser/releases/download/$(CSVPARSER_VER)/csv.hpp
	@echo "$(CSVPARSER_SHA256)  $@" | shasum -a 256 -c - \
	  || { echo "csv.hpp checksum mismatch -- refusing to use it"; rm -f $@; exit 1; }

bench-build: ocaml-build crane-build $(CSVPARSER_HDR)
	c++ -O2 -std=c++17 $(SIMDJSON_FLAGS) -o _build/default/run_json_ref.exe run_json_ref.cpp
	c++ -O2 -std=c++17 $(XML2_FLAGS)     -o _build/default/run_xml_ref.exe  run_xml_ref.cpp
	c++ -O2 -std=c++17 $(PUGIXML_FLAGS)  -o _build/default/run_xml_pugi.exe run_xml_pugi.cpp
	c++ -O2 -std=c++17 -pthread -Ivendor/csv-parser -o _build/default/run_csv_ref.exe run_csv_ref.cpp

# ---------------------------------------------------------------
# Interned-DFA closure certificate report
# ---------------------------------------------------------------
closure-check: coq-extract
	dune build ./run_closure.exe && ./_build/default/run_closure.exe

# ---------------------------------------------------------------
# Corpus staging. Curates the pinned corpus-src/ submodules into a flat,
# parser-acceptable corpus under $(DATA)/{JSON,CSV,XML}/{Instances,SmallInstances}.
# Depends on bench-build (ocaml-build + crane-build): stage_data.py uses the built
# runners as the authoritative "does the grammar accept this file?" filter -- the
# fast OCaml runner for small files, and the C++ (Crane) runner for the large
# rungs the OCaml runner would stack-overflow on. Run once after
# `git submodule update --init` (and again if you re-pin a submodule).
# ---------------------------------------------------------------
STAGE := python3 stage_data.py

stage-data: bench-build ; DATA=$(DATA) $(STAGE) all
stage-json: bench-build ; DATA=$(DATA) $(STAGE) json
stage-csv:  bench-build ; DATA=$(DATA) $(STAGE) csv
stage-xml:  bench-build ; DATA=$(DATA) $(STAGE) xml

# ---------------------------------------------------------------
# Benchmarks. DATA points at a corpus directory laid out as
#   $(DATA)/{JSON,CSV,XML}/{Instances,SmallInstances}
# Populate it with `make stage-data` (from the pinned corpus-src/ submodules)
# or point DATA at your own corpus (README.md).
# ---------------------------------------------------------------
DATA        ?= ./data
BENCH_FLAGS ?= --warmup 3 --runs 10
BENCH       := _build/default/bench.exe

bench: bench-json bench-json-small bench-csv bench-csv-small \
       bench-xml bench-xml-small

bench-json: bench-build
	$(BENCH) -json $(DATA)/JSON/Instances json_results.json $(BENCH_FLAGS)
bench-json-small: bench-build
	$(BENCH) -json $(DATA)/JSON/SmallInstances json_results_small.json $(BENCH_FLAGS)
bench-csv: bench-build
	$(BENCH) -csv $(DATA)/CSV/Instances csv_results.json $(BENCH_FLAGS)
bench-csv-small: bench-build
	$(BENCH) -csv $(DATA)/CSV/SmallInstances csv_results_small.json $(BENCH_FLAGS)
bench-xml: bench-build
	$(BENCH) -xml $(DATA)/XML/Instances xml_results.json $(BENCH_FLAGS)
bench-xml-small: bench-build
	$(BENCH) -xml $(DATA)/XML/SmallInstances xml_results_small.json $(BENCH_FLAGS)

# ---------------------------------------------------------------
clean:
	-$(MAKE) -f CoqMakefile clean 2>/dev/null || true
	rm -f CoqMakefile CoqMakefile.conf
	rm -rf _build extracted crane_extracted
	find . -maxdepth 1 -name '*.vo' -delete
	find . -maxdepth 1 -name '*.vok' -delete
	find . -maxdepth 1 -name '*.vos' -delete
	find . -maxdepth 1 -name '*.glob' -delete
	find . -maxdepth 1 -name '.*.aux' -delete
