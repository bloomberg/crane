#pragma once

#include "fn.h"
#include <cstdint>
#include <deque>
#include <utility>

struct DequeFoldCurriedAcc {
  static uint64_t g(const std::deque<uint64_t> &l, uint64_t x0_, bool x1_);
  static inline const uint64_t result = g(
      [](auto _a0, auto _a1) {
        _a1.push_front(_a0);
        return _a1;
      }(UINT64_C(1), [](auto _a0, auto _a1) {
        _a1.push_front(_a0);
        return _a1;
      }(UINT64_C(2), std::deque<uint64_t>{})),
      UINT64_C(3),
      true);
};
