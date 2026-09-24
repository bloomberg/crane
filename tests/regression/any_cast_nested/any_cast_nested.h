#ifndef INCLUDED_ANY_CAST_NESTED
#define INCLUDED_ANY_CAST_NESTED

#include "crane_fn.h"
#include <any>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A, typename P> struct SigT;

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  template <typename _U0, typename _U1> operator SigT<_U0, _U1>() const {
    return {[&]() -> _U0 {
              if constexpr (crane_convertible<_U0, const A &>) {
                return crane_convert<_U0>(x);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }(),
            [&]() -> _U1 {
              if constexpr (crane_convertible<_U1, const P &>) {
                return crane_convert<_U1>(a1);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
  }

  // CREATORS
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }
};

struct AnyCastNested {
  template <typename a = void> using payload_ty = std::any;

  template <typename T1>
  static T1 extract_a(const SigT<uint64_t, payload_ty<T1>> &s) {
    const auto &[x0, a1] = s;
    auto _cs = std::any_cast<uint64_t>(x0);
    if (_cs <= 0) {
      const auto &[_x, rest] = std::any_cast<std::pair<std::any, std::any>>(a1);
      const auto &[_x0, v] = std::any_cast<std::pair<std::any, std::any>>(rest);
      return std::any_cast<T1>(v);
    } else {
      uint64_t _x = _cs - 1;
      return std::any_cast<T1>(a1);
    }
  }

  static uint64_t test_extract(uint64_t x);
};

#endif // INCLUDED_ANY_CAST_NESTED
