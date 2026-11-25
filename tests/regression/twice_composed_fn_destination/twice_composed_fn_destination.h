#pragma once

#include "fn.h"
#include <cstdint>
#include <type_traits>
#include <utility>

struct TwiceComposedFnDestination {
  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1> &&
             std::is_invocable_r_v<T1, F0 &, const T1 &>
  static T1 twice(F0 &&f, const T1 &x) {
    return f(f(x));
  }

  static uint64_t h(uint64_t k, uint64_t x0_);
  static inline const uint64_t result = h(UINT64_C(2), UINT64_C(5));
};
