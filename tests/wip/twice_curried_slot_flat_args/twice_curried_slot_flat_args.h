#pragma once

#include "fn.h"
#include <cstdint>
#include <type_traits>
#include <utility>

struct TwiceCurriedSlotFlatArgs {
  template <typename T1> static T1 pick(bool b, T1 x, T1 y) {
    if (b) {
      return x;
    } else {
      return y;
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1> &&
             std::is_invocable_r_v<T1, F0 &, const T1 &>
  static T1 twice(F0 &&f, const T1 &x) {
    return f(f(x));
  }

  template <typename F0> static uint64_t h(F0 &&, uint64_t) {
    return UINT64_C(4);
  }

  static inline const uint64_t d = []() {
    return twice<crane::fn<uint64_t(uint64_t)>>(
        twice<crane::fn<
            crane::fn<uint64_t(uint64_t)>(crane::fn<uint64_t(uint64_t)>)>>(
            [](crane::fn<uint64_t(crane::fn<uint64_t(uint64_t)>,
                                  uint64_t)> _x0) {
              return [=](crane::fn<uint64_t(uint64_t)> _x1,
                         uint64_t _x2)
                          -> uint64_t {
                return pick<crane::fn<
                    uint64_t(crane::fn<uint64_t(uint64_t)>, uint64_t)>>(
                    true,
                    [](crane::fn<uint64_t(uint64_t)> _ec0,
                       uint64_t _ec1) { return h(_ec0, _ec1); },
                    _x0)(_x1, _x2);
              };
            },
            [](crane::fn<uint64_t(uint64_t)> _ec0) {
              return [=, _ec0 = std::move(_ec0)](uint64_t _ec1) {
                return h(_ec0, _ec1);
              };
            }),
        [](uint64_t) { return UINT64_C(5); })(UINT64_C(3));
  }();
};
