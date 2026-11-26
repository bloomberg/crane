#pragma once

#include "fn.h"
#include <cstdint>
#include <type_traits>
#include <utility>

struct TwiceTransformerTwoArg {
  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1> &&
             std::is_invocable_r_v<T1, F0 &, const T1 &>
  static T1 twice(F0 &&f, const T1 &x) {
    return f(f(x));
  }

  static inline const uint64_t result = []() {
    return twice<crane::fn<uint64_t(bool, uint64_t)>>(
        twice<crane::fn<crane::fn<uint64_t(bool, uint64_t)>(
            crane::fn<uint64_t(bool, uint64_t)>)>>(
            [](crane::fn<crane::fn<uint64_t(bool, uint64_t)>(
                crane::fn<uint64_t(bool, uint64_t)>)> k) {
              return [=, k = std::move(k)](
                  crane::fn<uint64_t(bool, uint64_t)> h) {
                return [=, k = k, h = std::move(h)](bool b,
                                                    uint64_t n) {
                  return (k(h)(b, n) + UINT64_C(1));
                };
              };
            },
            [](crane::fn<uint64_t(bool, uint64_t)> h) {
              return [=, h = std::move(h)](bool b,
                                           uint64_t n) {
                return (h(b, n) * UINT64_C(2));
              };
            }),
        [](bool, uint64_t n) { return n; })(true, UINT64_C(4));
  }();
};
