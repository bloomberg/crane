#pragma once

#include <cstdint>
#include <utility>

struct AliasParamConventionCheck {
  using t1 = std::pair<uint64_t, bool>;
  static uint64_t op1(t1 x0_);
  static inline const uint64_t result = op1(std::make_pair(UINT64_C(4), true));
};
