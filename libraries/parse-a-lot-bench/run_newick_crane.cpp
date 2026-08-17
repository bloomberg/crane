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
#include "Newick.h"

struct RunArgs { int argc; char **argv; int result; };

// Mirrors run_newick.ml's count_newick_node:
//   NkLeaf            -> 1
//   NkINode(desc, _)  -> 1 + sum of counts of descendants
static long count_newick_node(const Newick::Newick_node &n) {
    using NN = Newick::Newick_node;
    const auto &v = n.v();
    if (const auto *ino = std::get_if<NN::NkINode>(&v)) {
        long c = 1;
        for (const auto &d : ino->descendants) c += count_newick_node(d);
        return c;
    }
    return 1;
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

    try {
    std::optional<crane::list<Newick::D::Defs::token>> ts_opt;
    {
        // Lexing is the only phase that touches the arena-mode `regex`/DFA
        // table. Tokens are plain data (terminal tag + int/string/unit
        // payload, regex-free), so the lexer's arena can be dropped in O(1)
        // as soon as lexing finishes instead of being held open through the
        // whole parse phase too.
        crane::arena_scope _lex_arena;
        auto [ts, _rest] = Newick::lex_newick(input);
        ts_opt = std::move(ts);
    }
    if (!ts_opt.has_value()) {
        fprintf(stderr, "Lex failure\n");
        a->result = 1;
        return nullptr;
    }
    long num_tokens = static_cast<long>(ts_opt->size());

    crane::arena_scope _parse_arena;
    auto pr = Newick::parse_newick(*ts_opt);

    using PR = Newick::Newick_Parser::ParserAndProofs::PEF::PS::P::Parse_result;
    const char *kind = nullptr;
    const std::any *val = nullptr;
    if (const auto *u = std::get_if<PR::Unique>(&pr.v())) {
        kind = "unique"; val = &u->a0;
    } else if (const auto *am = std::get_if<PR::Ambig>(&pr.v())) {
        kind = "ambig";  val = &am->a0;
    }
    if (kind) {
        // nt_semty of the start symbol is (list newick_tree). A top-level list
        // semty erases its ELEMENTS to std::any, so the value is a
        // std::deque<std::any>, each holding a concrete Newick_tree (whose .a0
        // is the concrete newick_node list). Unlike OCaml (which unwraps the
        // single-constructor newick_tree), the C++ Newick_tree keeps a .a0
        // field. Sum node counts across all trees, mirroring run_newick.ml.
        const auto &trees =
            std::any_cast<const crane::list<std::any> &>(*val);
        long nodes = 0;
        for (const auto &tree_any : trees) {
            const auto &tree = std::any_cast<const Newick::Newick_tree &>(tree_any);
            for (const auto &n : tree.a0) nodes += count_newick_node(n);
        }
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
        fprintf(stderr, "Usage: %s <file.newick>\n", argv[0]);
        return 1;
    }

    RunArgs args = {argc, argv, 1};
    pthread_t thread;
    pthread_attr_t attr;
    pthread_attr_init(&attr);
    pthread_attr_setstacksize(&attr, 2UL * 1024 * 1024 * 1024);
    pthread_create(&thread, &attr, run_main, &args);
    pthread_attr_destroy(&attr);
    pthread_join(thread, nullptr);
    return args.result;
}
