#include "loopify_gap_pair_destructure.h"

std::pair<uint64_t, uint64_t> LoopifyGapPairDestructure::swap_pair(uint64_t n) {
  if (n <= 0) {
    return std::make_pair(UINT64_C(0), UINT64_C(0));
  } else {
    uint64_t m = n - 1;
    auto [a, b] = swap_pair(m);
    return std::make_pair(b, (a + 1));
  }
}
