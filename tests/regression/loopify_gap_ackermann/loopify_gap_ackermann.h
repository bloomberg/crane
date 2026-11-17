#pragma once

#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <utility>
#include <variant>

struct LoopifyGapAckermann {
  static uint64_t ack(uint64_t m, uint64_t x0_);
};
