#pragma once

#include <cstdint>

struct Nat {};

struct EqDecSelfWerror {
  static uint64_t f(uint64_t x);
  static inline const uint64_t result = f(UINT64_C(4));
};
