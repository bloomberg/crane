#pragma once

#include "fn.h"
#include <cstdint>
#include <deque>
#include <utility>

struct DequeFoldFixInit {
  static uint64_t compose_all(const std::deque<uint64_t> &l,
                              const std::deque<uint64_t> &base, uint64_t x0_);
  static inline const uint64_t t_1 = compose_all(
      [](auto _a0, auto _a1) {
        _a1.push_front(_a0);
        return _a1;
      }(UINT64_C(1), [](auto _a0, auto _a1) {
        _a1.push_front(_a0);
        return _a1;
      }(UINT64_C(2), [](auto _a0, auto _a1) {
        _a1.push_front(_a0);
        return _a1;
      }(UINT64_C(3), std::deque<uint64_t>{}))),
      [](auto _a0, auto _a1) {
        _a1.push_front(_a0);
        return _a1;
      }(UINT64_C(10), std::deque<uint64_t>{}),
      UINT64_C(100));
  static std::deque<uint64_t> with_let(bool b, const std::deque<uint64_t> &x0_);
  static inline const uint64_t t_2 =
      static_cast<uint64_t>(with_let(false, std::deque<uint64_t>{}).size());
};
