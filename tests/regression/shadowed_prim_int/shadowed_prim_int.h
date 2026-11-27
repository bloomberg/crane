#pragma once

#include <cstdint>

struct ShadowedPrimInt {
  static constexpr int64_t big = INT64_C(300);
  static inline const int64_t sum =
      static_cast<int64_t>((static_cast<uint64_t>(big) + UINT64_C(1)) &
                           UINT64_C(9223372036854775807));
};
