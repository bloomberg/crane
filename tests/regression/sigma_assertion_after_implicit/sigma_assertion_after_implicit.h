#pragma once

#include <cassert>
#include <cstdint>

struct SigmaAssertionAfterImplicit {
  static uint64_t f(uint64_t x, uint64_t y);
  static inline const uint64_t test = f(UINT64_C(7), UINT64_C(1));
};
