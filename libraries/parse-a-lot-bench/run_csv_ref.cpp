// SPDX-License-Identifier: BSD-3-Clause
//
// CSV reference baseline: Vince La's csv-parser (vincentlaucsb/csv-parser, MIT).
// The single-header `csv.hpp` is fetched into vendor/csv-parser/ by the Makefile
// (`make vendor/csv-parser/csv.hpp`) and is NOT committed here; see that file's
// LICENSE. This is the third-party "how fast can an optimized C++ CSV reader do
// it" baseline the report compares the verified ParseALot pipeline against.
#include "csv.hpp"
#include <cstdio>
#include <cstdlib>

/*
 * Parse the whole file and touch every field so the compiler cannot elide the
 * work. csv-parser streams rows lazily (memory-mapped, with a worker thread),
 * so iterating to exhaustion is what forces a full parse. We report the field
 * count as `parse_nodes` purely as a work proxy -- it is not meant to equal the
 * ParseALot parse-tree node count (each parser counts nodes its own way); the
 * report's shared node/token columns come from the ParseALot back ends, and the
 * reference contributes only wall-clock + peak RSS + a success signal.
 */
int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr, "Usage: %s <file.csv>\n", argv[0]);
        return 1;
    }
    try {
        csv::CSVReader reader(argv[1]);
        long long rows = 0, fields = 0;
        for (csv::CSVRow &row : reader) {
            rows++;
            fields += static_cast<long long>(row.size());
        }
        volatile long long sink = fields;   // defeat dead-code elimination
        (void)sink;
        printf("{\"parse_result\":\"ok\",\"parse_nodes\":%lld,"
               "\"num_tokens\":%lld}\n", rows + fields, fields);
        return 0;
    } catch (const std::exception &e) {
        fprintf(stderr, "csv-parser: %s\n", e.what());
        return 1;
    }
}
