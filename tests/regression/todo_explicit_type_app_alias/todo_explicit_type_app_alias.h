#pragma once

#include <cstdint>

struct TodoExplicitTypeAppAlias {
  template <typename T1> static T1 id(T1 x) { return x; }

  static inline const uint64_t test_value = []() {
    uint64_t kept_nat = id(UINT64_C(9));
    bool kept_bool = id(true);
    return (kept_nat + (kept_bool ? UINT64_C(1) : UINT64_C(0)));
  }();
};
