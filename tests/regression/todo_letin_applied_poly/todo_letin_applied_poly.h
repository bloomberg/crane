#pragma once

#include <cstdint>

struct TodoLetinAppliedPoly {
  static constexpr uint64_t demo_nat = UINT64_C(7);
  static constexpr bool demo_bool = true;
  static inline const uint64_t test_value =
      (demo_bool ? demo_nat : UINT64_C(0));
};
