// SPDX-License-Identifier: BSD-3-Clause
#include <simdjson.h>
#include <cstdio>
#include <cstdlib>
#include <unordered_set>
#include <string_view>

using namespace simdjson;

/*
 * count_nodes — recursive DOM traversal with duplicate-key detection
 *
 * Returns the total number of JSON nodes (objects, arrays, and scalars each
 * count as 1), or -1 if a duplicate key is found anywhere in the document.
 *
 * This mirrors the semantic constraint enforced by the Rocq/parse-a-lot JSON
 * parser: the `nodupKeys` predicate rejects any object whose key list contains
 * a repeated string.  Without this check the comparison would be unfair —
 * simdjson would accept inputs that parse-a-lot rejects.
 */
static int count_nodes(dom::element e) {
    switch (e.type()) {

        case dom::element_type::OBJECT: {
            /*
             * Duplicate-key detection with std::unordered_set<std::string_view>
             *
             * WHY string_view, not string?
             *   simdjson stores all string data in a single heap-allocated
             *   "tape" that is a padded copy of the input.  A string_view is
             *   just (pointer, length) into that buffer — no per-key heap
             *   allocation.  Using std::string instead would copy every key
             *   onto the heap: O(k) allocation per key where k = key length.
             *
             * Time complexity per object with n keys of average length k:
             *   - std::hash<std::string_view> reads all k bytes: O(k) per key.
             *   - unordered_set::insert: O(k) amortized (hash + equality probe).
             *   - Total for one object: O(n·k) amortized.
             *   - Worst case with pathological hash collisions: O(n²·k), but
             *     std::hash on string_view uses a high-quality hash (e.g.
             *     FNV-1a or similar) making collisions astronomically rare in
             *     practice.
             *
             * Why not sort-then-scan?
             *   Sorting n string_views costs O(n·k·log n) comparisons, which
             *   is strictly worse than O(n·k) amortized for the hash set.
             *   Sorting also requires O(n) extra space for the vector, while
             *   the hash set uses O(n) space too but avoids the log factor.
             *
             * Space complexity:
             *   The `seen` set is a local variable destroyed on return, so
             *   sets at different nesting levels do not accumulate.  At any
             *   point during recursion the live sets form a stack of depth D
             *   (= current nesting level), each holding at most N_max entries.
             *   Peak space: O(D·N_max·sizeof(string_view)) = O(D·N_max·16).
             *   In real JSON D and N_max are both small (JSON nesting rarely
             *   exceeds ~20 levels; typical objects have tens of keys).
             *
             * Total cost over the whole document:
             *   Summing across all objects, the total work is O(sum of all
             *   key lengths across the entire document), which is bounded by
             *   O(input size).  This matches the O(n) traversal cost of
             *   count_nodes itself, so duplicate detection adds no asymptotic
             *   overhead.
             */
            std::unordered_set<std::string_view> seen;
            int n = 1;
            for (auto [key, val] : dom::object(e)) {
                if (!seen.insert(key).second)
                    return -1;   /* duplicate key — reject the document */
                int sub = count_nodes(val);
                if (sub < 0) return -1;   /* propagate rejection from nested value */
                n += sub;
            }
            return n;
        }

        case dom::element_type::ARRAY: {
            /*
             * Arrays have no semantic constraints beyond the CFG, so we just
             * count recursively.  Cost: O(total nodes in the array subtree).
             */
            int n = 1;
            for (auto val : dom::array(e)) {
                int sub = count_nodes(val);
                if (sub < 0) return -1;   /* propagate rejection from element */
                n += sub;
            }
            return n;
        }

        default:
            /*
             * Scalars (string, number, bool, null) — O(1).
             * simdjson has already validated their format during parsing
             * (e.g. UTF-8 for strings, IEEE 754 range for numbers), so no
             * further semantic check is needed here.
             */
            return 1;
    }
}

int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr, "Usage: %s <file.json>\n", argv[0]);
        return 1;
    }

    /*
     * simdjson DOM parser.
     *
     * parser.load() reads the file, makes a padded copy of the input
     * (SIMDJSON_PADDING extra bytes so SIMD reads never go out of bounds),
     * runs the two-pass SIMD structural indexing + tape builder, and returns
     * a fully materialised DOM.  All of that is O(n) in the input size.
     *
     * The DOM lives inside `parser`'s internal buffers, which is why
     * string_views into the tape remain valid for the lifetime of `parser`.
     */
    dom::parser parser;
    dom::element doc;
    auto err = parser.load(argv[1]).get(doc);
    if (err) {
        fprintf(stderr, "simdjson error: %s\n", error_message(err));
        return 1;
    }

    /*
     * count_nodes is O(input size) amortized (see above).
     * `volatile` prevents the compiler from dead-code-eliminating the call
     * since the result is otherwise unused.
     */
    int n = count_nodes(doc);
    if (n < 0) {
        fprintf(stderr, "rejected: duplicate object key\n");
        return 1;
    }
    /* Emit a result line so report_bench.py can read the outcome, matching the
     * OCaml/Crane runners' convention. `parse_nodes` here is simdjson's DOM node
     * count; it need not equal ParseALot's (the report's shared node column comes
     * from the ParseALot back ends). */
    printf("{\"parse_result\":\"ok\",\"parse_nodes\":%d}\n", n);
    return 0;
}
