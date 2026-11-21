#pragma once

#include <cstdint>
#include <persistent_array.h>

struct PrimArrayDefault {
  static inline const persistent_array<uint64_t> arr =
      persistent_array<uint64_t>(INT64_C(2), UINT64_C(7));
  static inline const uint64_t dflt = arr.default_value();
};
