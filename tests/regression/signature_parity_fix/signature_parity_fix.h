#pragma once

#include <cstdint>

struct SignatureParityFix {
  static uint64_t f(uint64_t seed);
  static inline const uint64_t t = f(UINT64_C(4));
};
