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
#include "JSON.h"

struct RunArgs { int argc; char **argv; int result; };

// Count parse-tree nodes, mirroring run_json.ml's count_json_nodes:
//   JAssoc -> 1 + sum of counts of the pair values
//   JList  -> 1 + sum of counts of the elements
//   other  -> 1
static long count_json_nodes(const JSON::Json_value &jv) {
    using JV = JSON::Json_value;
    const auto &v = jv.v();
    if (const auto *a = std::get_if<JV::JAssoc>(&v)) {
        long n = 1;
        for (const auto &kv : a->a0) n += count_json_nodes(kv.second);
        return n;
    } else if (const auto *l = std::get_if<JV::JList>(&v)) {
        long n = 1;
        for (const auto &e : l->a0) n += count_json_nodes(e);
        return n;
    }
    return 1;
}

static void *run_main(void *arg) {
    auto *a = static_cast<RunArgs *>(arg);
    int argc = a->argc;
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

    // A/B probe: ONE caller-owned region for the whole job (lex + parse +
    // consume). Nothing escapes it, so cons cells need no per-cell keeper (
    // arena_use_scope publishes a null keeper slot). Region freed at function end.
    crane::arena _region;
    crane::arena_use_scope _scope(_region);
    try {
    std::optional<crane::list<JSON::D::Defs::token>> ts_opt;
    {
        auto [ts, _rest] = JSON::lex_json(input);
        ts_opt = std::move(ts);
    }
    if (!ts_opt.has_value()) {
        fprintf(stderr, "Lex failure\n");
        a->result = 1;
        return nullptr;
    }
    long num_tokens = static_cast<long>(ts_opt->size());

    auto pr = JSON::parse_json(*ts_opt);

    using PR = JSON::JSON_Parser::ParserAndProofs::PEF::PS::P::Parse_result;
    const char *kind = nullptr;
    const std::any *val = nullptr;
    if (const auto *u = std::get_if<PR::Unique>(&pr.v())) {
        kind = "unique"; val = &u->a0;
    } else if (const auto *am = std::get_if<PR::Ambig>(&pr.v())) {
        kind = "ambig";  val = &am->a0;
    }
    if (kind) {
        // Emit a metadata line (matching run_json.ml / bench_common.ml) so the
        // benchmark harness can cross-check OCaml vs C++ results.
        long nodes = count_json_nodes(std::any_cast<const JSON::Json_value &>(*val));
        printf("{\"parse_result\":\"%s\",\"num_tokens\":%ld,\"parse_nodes\":%ld,\"ref_nodes\":null}\n",
               kind, num_tokens, nodes);
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
        fprintf(stderr, "Usage: %s <file.json>\n", argv[0]);
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
