#ifndef INCLUDED_EXISTENTIAL_FN_PROJECTION
#define INCLUDED_EXISTENTIAL_FN_PROJECTION

#include "crane_fn.h"
#include <any>
#include <functional>
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

  P projT2() const {
    const auto &[x0, a1] = *this;
    return a1;
  }
};

struct ExistentialFnProjection {
  static inline const SigT<std::any, std::any> measurer =
      SigT<std::any, std::any>::existt(
          std::any(), crane_erase_fn([](const std::any &_any_x) -> uint64_t {
            uint64_t x = std::any_cast<uint64_t>(_any_x);
            return (std::any_cast<uint64_t>(x) + UINT64_C(1));
          }));
  static inline const uint64_t measured =
      std::any_cast<uint64_t>(std::any_cast<std::function<std::any(std::any)>>(
          measurer.projT2())(std::any(UINT64_C(4))));
  static inline const SigT<std::any, std::pair<std::any, std::any>> tagged =
      SigT<std::any, std::pair<std::any, std::any>>::existt(
          std::any(),
          std::make_pair(std::any(UINT64_C(7)), std::any(UINT64_C(8))));
  static inline const uint64_t tag = std::any_cast<uint64_t>(
      crane_any_cast<std::pair<std::any, std::any>>(tagged.projT2()).second);
};

#endif // INCLUDED_EXISTENTIAL_FN_PROJECTION
