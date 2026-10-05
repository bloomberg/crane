#ifndef INCLUDED_DUPLICATE_OUTPUT_TARGET
#define INCLUDED_DUPLICATE_OUTPUT_TARGET

#include <cstdint>

struct First {
  static constexpr uint64_t one = UINT64_C(1);
};

struct Second {
  static constexpr uint64_t two = UINT64_C(2);
};

#endif // INCLUDED_DUPLICATE_OUTPUT_TARGET
