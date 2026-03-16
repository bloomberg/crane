#include "pendant_sumtree_roundtrip.h"

#include <cassert>

int main() {
    assert(PendantSumtreeRoundtripCase::sample_multi_roundtrip_ok);
    assert(PendantSumtreeRoundtripCase::sample_group_valid);
    assert(PendantSumtreeRoundtripCase::sample_subtree_valid);
    assert(PendantSumtreeRoundtripCase::sample_tree_valid);
    assert(PendantSumtreeRoundtripCase::sample_leaf_total_matches_root);
    assert(PendantSumtreeRoundtripCase::sample_tree_depth == 3u);
    assert(PendantSumtreeRoundtripCase::sample_ledger_entry_count == 3u);
    assert(PendantSumtreeRoundtripCase::sample_ledger_all_present);
    return 0;
}
