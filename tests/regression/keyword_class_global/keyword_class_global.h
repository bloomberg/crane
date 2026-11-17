#pragma once

#include <cstdint>

struct KeywordClassGlobal {
  static uint64_t class_(uint64_t n);
  static inline const uint64_t t = class_(UINT64_C(4));
};
