#pragma once

#include "fn.h"
#include <cstdint>
#include <type_traits>

struct TwiceFnTransformerStep {
  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1> &&
             std::is_invocable_r_v<T1, F0 &, const T1 &>
  static T1 twice(F0 &&f, const T1 &x) {
    return f(f(x));
  }

  static inline const uint64_t result = []() {
    return twice<crane::fn<uint64_t(uint64_t)>>(
        [](crane::fn<uint64_t(uint64_t)> _x0) {
          return [=](uint64_t _x1) -> uint64_t {
            return twice<crane::fn<
                crane::fn<uint64_t(uint64_t)>(crane::fn<uint64_t(uint64_t)>)>>(
                [](crane::fn<uint64_t(crane::fn<uint64_t(uint64_t)>,
                                      uint64_t)>) {
                  return [](const crane::fn<uint64_t(uint64_t)> &h,
                            uint64_t n) { return h((n + 1)); };
                },
                [](crane::fn<uint64_t(uint64_t)> h) { return h; })(_x0, _x1);
          };
        },
        [](uint64_t n) { return (n * UINT64_C(10)); })(UINT64_C(1));
  }();
};
