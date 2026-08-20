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
#include "XML.h"

struct RunArgs { int argc; char **argv; int result; };

// Mirrors run_xml.ml's count_xml_nodes:
//   XmlNode(_, _, children) -> 1 + sum of counts of children
//   XmlLeaf                 -> 1
static long count_xml_nodes(const XML::Xml_tree &t) {
    using XT = XML::Xml_tree;
    const auto &v = t.v();
    if (const auto *node = std::get_if<XT::XmlNode>(&v)) {
        long c = 1;
        for (const auto &ch : node->children) c += count_xml_nodes(ch);
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
    std::optional<crane::list<XML::D::Defs::token>> ts_opt;
    {
        // Lexing is the only phase that touches the arena-mode `regex`/DFA
        // table. Tokens are plain data (terminal tag + int/string/unit
        // payload, regex-free), so the lexer's arena can be dropped in O(1)
        // as soon as lexing finishes instead of being held open through the
        // whole parse phase too.
        crane::arena_scope _lex_arena;
        auto [ts, _rest] = XML::lex_xml(input);
        ts_opt = std::move(ts);
    }
    if (!ts_opt.has_value()) {
        fprintf(stderr, "Lex failure\n");
        a->result = 1;
        return nullptr;
    }
    long num_tokens = static_cast<long>(ts_opt->size());

    crane::arena_scope _parse_arena;
    auto pr = XML::parse_xml(*ts_opt);

    using PR = XML::XML_Parser::ParserAndProofs::PEF::PS::P::Parse_result;
    const char *kind = nullptr;
    const std::any *val = nullptr;
    if (const auto *u = std::get_if<PR::Unique>(&pr.v())) {
        kind = "unique"; val = &u->a0;
    } else if (const auto *am = std::get_if<PR::Ambig>(&pr.v())) {
        kind = "ambig";  val = &am->a0;
    }
    if (kind) {
        // Fingerprint mirrors run_xml.ml: count nodes of the document root element.
        const auto &doc = std::any_cast<const XML::Xml_document &>(*val);
        long nodes = count_xml_nodes(doc.elt);
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
        fprintf(stderr, "Usage: %s <file.xml>\n", argv[0]);
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
