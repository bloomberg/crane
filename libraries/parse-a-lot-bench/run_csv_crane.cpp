// SPDX-License-Identifier: BSD-3-Clause
#include <cstdio>
#include <cstdlib>
#include <deque>
#include <fstream>
#include <string>
#include <stdexcept>
#include <variant>
#include <pthread.h>
#include <immer/flex_vector.hpp>
#include <immer/box.hpp>

#include "arena.h"
#include "conslist.h"
#include "CSV.h"

struct RunArgs { int argc; char **argv; int result; };

// The CSV start symbol [Csv] has semantic type [list (list string)]. The
// generic CoStar++ parser stores every nonterminal value type-erased, so each
// list level is a [crane::list<std::any>]: the outer any holds the rows list,
// each row-any holds a fields list, and each field-any holds a std::string.
using ErasedList = crane::list<std::any>;

// Fingerprint = total number of fields (sum of record lengths), mirroring
// run_csv.ml's count_fields.
static long count_fields(const std::any &top) {
    long n = 0;
    auto rows = std::any_cast<ErasedList>(top);
    for (const auto &row_any : rows) {
        auto fields = std::any_cast<ErasedList>(row_any);
        n += static_cast<long>(fields.size());
    }
    return n;
}

static void *run_main(void *arg) {
    auto *a = static_cast<RunArgs *>(arg);
    char **argv = a->argv;

    std::ifstream ifs(argv[1], std::ios::binary);
    if (!ifs) {
        fprintf(stderr, "Cannot open %s\n", argv[1]);
        a->result = 1;
        return nullptr;
    }
    std::string raw((std::istreambuf_iterator<char>(ifs)),
                     std::istreambuf_iterator<char>());

    auto input = crane::list<char>::from_range(raw.begin(), raw.end());

    // One caller-owned region for the whole job (lex + parse + consume); nothing
    // escapes it. Region freed at function end. See run_json_crane.cpp.
    crane::arena _region;
    crane::arena_use_scope _scope(_region);
    try {
    std::optional<crane::list<CSV::D::Defs::token>> ts_opt;
    {
        auto [ts, _rest] = CSV::lex_csv(input);
        ts_opt = std::move(ts);
    }
    if (!ts_opt.has_value()) {
        fprintf(stderr, "Lex failure\n");
        a->result = 1;
        return nullptr;
    }
    long num_tokens = static_cast<long>(ts_opt->size());

    auto pr = CSV::parse_csv(*ts_opt);

    using PR = CSV::CSV_Parser::ParserAndProofs::PEF::PS::P::Parse_result;
    const char *kind = nullptr;
    const std::any *val = nullptr;
    if (const auto *u = std::get_if<PR::Unique>(&pr.v())) {
        kind = "unique"; val = &u->a0;
    } else if (const auto *am = std::get_if<PR::Ambig>(&pr.v())) {
        kind = "ambig";  val = &am->a0;
    }
    if (kind) {
        // Emit a metadata line (matching run_csv.ml / bench_common.ml) so the
        // benchmark harness can cross-check OCaml vs C++ results.
        long fields = count_fields(*val);
        printf("{\"parse_result\":\"%s\",\"num_tokens\":%ld,\"parse_nodes\":%ld,\"ref_nodes\":null}\n",
               kind, num_tokens, fields);
        fflush(stdout);
        a->result = 0;
        return nullptr;
    }
    fprintf(stderr, "Parse failure\n");
    a->result = 1;
    } catch (const std::bad_any_cast &e) {
        fprintf(stderr, "bad_any_cast: %s\n", e.what());
        a->result = 1;
    }
    return nullptr;
}

int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr, "Usage: %s <file.csv>\n", argv[0]);
        return 1;
    }

    RunArgs args = {argc, argv, 1};
    pthread_t thread;
    pthread_attr_t attr;
    pthread_attr_init(&attr);
    pthread_attr_setstacksize(&attr, 256 * 1024 * 1024);
    pthread_create(&thread, &attr, run_main, &args);
    pthread_attr_destroy(&attr);
    pthread_join(thread, nullptr);
    return args.result;
}
