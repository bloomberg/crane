// SPDX-License-Identifier: BSD-3-Clause
#include <cstdio>
#include <memory>
#include <libxml/parser.h>
#include <libxml/tree.h>

/*
 * RAII wrapper for xmlDocPtr.
 *
 * std::unique_ptr with a custom deleter calls xmlFreeDoc automatically when
 * the pointer goes out of scope — including on early returns and exceptions.
 * This is zero-overhead: the destructor call is inlined and the compiler
 * eliminates it entirely on the happy path where the process exits normally
 * (the OS reclaims memory anyway).  The benefit is correctness under tools
 * like AddressSanitizer or Valgrind, which track allocations until process
 * exit rather than stopping at the last free().
 */
struct XmlDocDeleter {
    void operator()(xmlDocPtr doc) const { xmlFreeDoc(doc); }
};
using XmlDocPtr = std::unique_ptr<xmlDoc, XmlDocDeleter>;

/*
 * count_nodes — recursive DOM traversal
 *
 * Returns the total number of XML nodes (elements, text nodes, comments, etc.
 * — everything that appears as an xmlNodePtr in the tree).
 *
 * The traversal serves two purposes:
 *   1. Prevents dead-code elimination: without a use of the parsed tree the
 *      compiler could theoretically hoist xmlReadFile into a no-op.
 *   2. Makes the workload comparable to parse-a-lot, which also walks the full
 *      parse tree to build an AST and evaluate semantic predicates.
 *
 * Tag-matching constraint:
 *   The Rocq/parse-a-lot XML parser enforces open/close tag name equality via
 *   `String.eqb nm nm'` on the element production.  libxml2 enforces the
 *   same constraint as part of its well-formedness check inside xmlReadFile —
 *   a document with mismatched tags is rejected before this function is ever
 *   called (xmlReadFile returns NULL).  There is therefore nothing extra to
 *   implement here; the constraint is already upheld at least as strictly as
 *   in parse-a-lot.
 *
 * Time complexity:
 *   The traversal visits every node exactly once.  At each node it recurses
 *   into node->children (first child) and then iterates node->next (siblings)
 *   in a loop rather than with a second recursive call, which keeps the call
 *   stack depth proportional to the nesting depth D rather than the total
 *   number of siblings.  In practice D is the XML element depth, which is
 *   small.  Total: O(N) where N = total number of nodes in the DOM.
 *
 * Space complexity:
 *   O(D) stack frames for the recursion into children.  The sibling iteration
 *   is a flat loop, so siblings do not consume stack space.
 *
 * Note on libxml2's internal tag-matching complexity:
 *   libxml2 maintains a tag stack during SAX-style parsing (even when building
 *   a DOM) and pops/compares on each closing tag.  Each comparison is O(k)
 *   where k = tag name length.  Total cost over the document: O(sum of all
 *   tag name lengths) = O(input size), same asymptotic class as parsing itself.
 */
static int count_nodes(xmlNodePtr node) {
    int n = 0;
    for (; node; node = node->next) {
        n += 1 + count_nodes(node->children);
    }
    return n;
}

int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr, "Usage: %s <file.xml>\n", argv[0]);
        return 1;
    }

    /*
     * xmlReadFile with the following flags:
     *
     *   XML_PARSE_NONET     — disable network access (DTD fetching etc.);
     *                         prevents unbounded latency on benchmark runs.
     *   XML_PARSE_NOWARNING — suppress non-fatal warning output to stderr,
     *                         which would pollute hyperfine's timing output.
     *   XML_PARSE_NOERROR   — suppress error messages to stderr for the same
     *                         reason; we check the return value instead.
     *
     * xmlReadFile is a single-pass SAX-driven DOM builder: it runs the expat-
     * style byte scanner, maintains a tag stack for well-formedness checking
     * (including open/close tag matching), and allocates DOM nodes into a
     * pool allocator (xmlMemBloc).  Total parsing cost: O(input size).
     *
     * Returns NULL on any well-formedness violation, including mismatched
     * tags, unclosed elements, illegal characters, and encoding errors.
     */
    XmlDocPtr doc(xmlReadFile(argv[1], NULL,
                              XML_PARSE_NONET |
                              XML_PARSE_NOWARNING |
                              XML_PARSE_NOERROR));
    if (!doc) {
        fprintf(stderr, "libxml2: failed to parse %s\n", argv[1]);
        return 1;
    }

    /*
     * count_nodes is O(N) in the number of DOM nodes (see above).
     * `volatile` prevents the compiler from eliminating the call.
     */
    volatile int n = count_nodes(xmlDocGetRootElement(doc.get()));
    (void)n;

    /*
     * doc goes out of scope here: XmlDocDeleter calls xmlFreeDoc, which walks
     * the DOM and frees every node and its string data — O(N).
     *
     * xmlCleanupParser releases libxml2's global state (encoding handler hash
     * tables etc.): O(1) amortized.  Called explicitly after the doc is freed
     * so the global state outlives any per-document data that references it.
     */
    xmlCleanupParser();
    return 0;
}
