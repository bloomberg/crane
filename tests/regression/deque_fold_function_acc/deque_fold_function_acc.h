#pragma once

#include "fn.h"
#include <cstdint>
#include <deque>
#include <type_traits>
#include <utility>

struct DequeFoldFunctionAcc {
  static uint64_t compose_all(const std::deque<uint64_t> &l, uint64_t x0_);
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
      UINT64_C(10));
  /// The same through fold_right, and with a global function as the
  /// initial value.
  static uint64_t compose_right(const std::deque<uint64_t> &l, uint64_t x0_);
  static uint64_t twice(uint64_t x);
  static uint64_t compose_glob(const std::deque<uint64_t> &l, uint64_t x0_);
  /// A list of functions built by the mapped map, applied.
  static std::deque<crane::fn<uint64_t(uint64_t)>>
  adders(const std::deque<uint64_t> &l);
  static inline const uint64_t t_2 =
      compose_right(
          [](auto _a0, auto _a1) {
            _a1.push_front(_a0);
            return _a1;
          }(UINT64_C(2), [](auto _a0, auto _a1) {
            _a1.push_front(_a0);
            return _a1;
          }(UINT64_C(3), std::deque<uint64_t>{})),
          UINT64_C(1)) +
      compose_glob(
          [](auto _a0, auto _a1) {
            _a1.push_front(_a0);
            return _a1;
          }(UINT64_C(1), std::deque<uint64_t>{}),
          UINT64_C(5)) +
      ([](auto _f, const auto &_l, auto _a) {
        for (const auto &_x : _l) _a = _f(_a, _x);
        return _a;
      }(
           [](uint64_t a,
              const crane::fn<uint64_t(uint64_t)> &f) { return f(a); },
           adders([](auto _a0, auto _a1) {
             _a1.push_front(_a0);
             return _a1;
           }(UINT64_C(1), [](auto _a0, auto _a1) {
             _a1.push_front(_a0);
             return _a1;
           }(UINT64_C(2), std::deque<uint64_t>{}))),
           UINT64_C(0)));
};
