#pragma once

#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <utility>
#include <variant>

struct LoopifyGapPairDestructure {
  static std::pair<uint64_t, uint64_t> swap_pair(uint64_t n);
};
