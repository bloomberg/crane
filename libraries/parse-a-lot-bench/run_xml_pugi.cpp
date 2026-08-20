// SPDX-License-Identifier: BSD-3-Clause
//
// XML reference baseline: pugixml (https://pugixml.org/, MIT). Installed as a
// system/brew dependency (see README prerequisites); pkg-config --libs pugixml.
// This is the third-party "how fast can an optimized C++ XML parser do it"
// baseline the report compares the verified ParseALot pipeline against. (The
// harness also ships a libxml2 baseline, run_xml_ref.cpp; pugixml is the DOM
// parser the report uses because it is the fastest common C++ option.)
#include "pugixml.hpp"
#include <cstdio>

/*
 * Recursive DOM traversal: visit every node so the parse cannot be elided, and
 * so the workload is comparable to ParseALot walking its full parse tree. The
 * count is a work proxy, not a match for ParseALot's parse_nodes (see the CSV
 * baseline note); the report takes shared node/token columns from the ParseALot
 * back ends and uses the reference only for wall-clock + peak RSS + success.
 */
static long count_nodes(const pugi::xml_node &node) {
    long n = 1;
    for (pugi::xml_node child : node.children())
        n += count_nodes(child);
    return n;
}

int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr, "Usage: %s <file.xml>\n", argv[0]);
        return 1;
    }
    pugi::xml_document doc;
    pugi::xml_parse_result r = doc.load_file(argv[1]);
    if (!r) {
        fprintf(stderr, "pugixml: %s\n", r.description());
        return 1;
    }
    volatile long n = count_nodes(doc.document_element());
    (void)n;
    printf("{\"parse_result\":\"ok\",\"parse_nodes\":%ld}\n", (long)n);
    return 0;
}
