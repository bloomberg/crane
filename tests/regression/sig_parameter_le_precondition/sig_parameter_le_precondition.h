#pragma once

#include <cassert>
#include <cstdint>

struct SigParameterLePrecondition {
  static uint64_t get(uint64_t _x, uint64_t x0_);
  static uint64_t get2(uint64_t _x, uint64_t x0_);
  static inline const uint64_t result =
      get(UINT64_C(5), UINT64_C(3)) + get2(UINT64_C(0), UINT64_C(2));
};
