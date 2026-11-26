#pragma once

#include "fn.h"
#include <cstdint>
#include <deque>
#include <type_traits>
#include <utility>

struct DequeNilCurriedElement {
  template <typename T1> static T1 hd_or(T1 d, const std::deque<T1> &l) {
    if (l.empty()) {
      return d;
    } else {
      const T1 &x = l.front();
      std::deque<T1> _x = std::deque<T1>(l.begin() + 1, l.end());
      return x;
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1> &&
             std::is_invocable_r_v<T1, F0 &, const T1 &>
  static T1 twice(F0 &&f, const T1 &x) {
    return f(f(x));
  }

  static inline const uint64_t result = []() {
    return twice<crane::fn<uint64_t(uint64_t)>>(
        hd_or<crane::fn<
            crane::fn<uint64_t(uint64_t)>(crane::fn<uint64_t(uint64_t)>)>>(
            [](crane::fn<uint64_t(uint64_t)> g) {
              return [=, g = std::move(g)](uint64_t n) {
                return (g(n) + UINT64_C(7));
              };
            },
            std::deque<crane::fn<
                crane::fn<uint64_t(uint64_t)>(crane::fn<uint64_t(uint64_t)>)>>{}),
        [](uint64_t n) { return (n * UINT64_C(2)); })(UINT64_C(3));
  }();
};
