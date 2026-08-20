#ifndef INCLUDED_LOOPIFY_GAP_PAIR_DESTRUCTURE
#define INCLUDED_LOOPIFY_GAP_PAIR_DESTRUCTURE

#include "small_vector.h"
#include <atomic>
#include <utility>
#include <variant>

struct LoopifyGapPairDestructure {
  static std::pair<uint64_t, uint64_t> swap_pair(uint64_t n);
};

#endif // INCLUDED_LOOPIFY_GAP_PAIR_DESTRUCTURE
