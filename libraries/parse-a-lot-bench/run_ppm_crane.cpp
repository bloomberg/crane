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
#include "PPM.h"

struct RunArgs { int argc; char **argv; int result; };

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

    try {
    std::optional<crane::list<PPM::D::Defs::token>> ts_opt;
    {
        // Lexing is the only phase that touches the arena-mode `regex`/DFA
        // table. Tokens are plain data (terminal tag + int/string/unit
        // payload, regex-free), so the lexer's arena can be dropped in O(1)
        // as soon as lexing finishes instead of being held open through the
        // whole parse phase too.
        crane::arena_scope _lex_arena;
        auto [ts, _rest] = PPM::lex_ppm(input);
        ts_opt = std::move(ts);
    }
    if (!ts_opt.has_value()) {
        fprintf(stderr, "Lex failure\n");
        a->result = 1;
        return nullptr;
    }
    long num_tokens = static_cast<long>(ts_opt->size());

    crane::arena_scope _parse_arena;
    auto pr = PPM::parse_ppm(*ts_opt);

    using PR = PPM::PPM_Parser::ParserAndProofs::PEF::PS::P::Parse_result;
    const char *kind = nullptr;
    const std::any *val = nullptr;
    if (const auto *u = std::get_if<PR::Unique>(&pr.v())) {
        kind = "unique"; val = &u->a0;
    } else if (const auto *am = std::get_if<PR::Ambig>(&pr.v())) {
        kind = "ambig";  val = &am->a0;
    }
    if (kind) {
        // Fingerprint mirrors run_ppm.ml: pixel count = length of triples.
        const auto &pv = std::any_cast<const PPM::ppm_value &>(*val);
        long nodes = static_cast<long>(pv.triples.size());
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
        fprintf(stderr, "Usage: %s <file.ppm>\n", argv[0]);
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
