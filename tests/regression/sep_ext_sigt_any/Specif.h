#ifndef INCLUDED_SPECIF
#define INCLUDED_SPECIF

#include "crane_fn.h"
#include <any>
#include <stdexcept>
#include <type_traits>
#include <utility>

namespace Specif {

template <typename A, typename P> struct SigT;

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  template <typename _U0, typename _U1> operator SigT<_U0, _U1>() const {
    return {[&]() -> _U0 {
              if constexpr (std::is_same_v<A, std::any>) {
                return crane_any_cast<_U0>(x);
              } else {
                if constexpr (std::is_constructible_v<_U0, const A &>) {
                  return _U0(x);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }
            }(),
            [&]() -> _U1 {
              if constexpr (std::is_same_v<P, std::any>) {
                return crane_any_cast<_U1>(a1);
              } else {
                if constexpr (std::is_constructible_v<_U1, const P &>) {
                  return _U1(a1);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }
            }()};
  }

  // CREATORS
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }
};

} // namespace Specif

#endif // INCLUDED_SPECIF
