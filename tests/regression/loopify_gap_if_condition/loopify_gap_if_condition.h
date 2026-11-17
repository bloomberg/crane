#pragma once

#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <utility>
#include <variant>

struct Nat {};

struct LoopifyGapIfCondition {
  static uint64_t parity(uint64_t n);
};
