#ifndef INCLUDED_LOOPIFY_GAP_PAIR_DESTRUCTURE
#define INCLUDED_LOOPIFY_GAP_PAIR_DESTRUCTURE

#include <utility>
#include <variant>
#include <vector>

struct LoopifyGapPairDestructure {
  static std::pair<uint64_t, uint64_t> swap_pair(uint64_t n);
};

#endif // INCLUDED_LOOPIFY_GAP_PAIR_DESTRUCTURE
