#ifndef INCLUDED_TODO_IOTA_COMPLEX_PATTERN
#define INCLUDED_TODO_IOTA_COMPLEX_PATTERN

#include "crane_fn.h"
#include <any>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct TodoIotaComplexPattern {
  template <typename A, typename B, typename C> struct Triple {
    // DATA
    A a0;
    B a1;
    C a2;

    // ACCESSORS
    Triple<A, B, C> clone() const { return {a0, a1, a2}; }

    template <typename _U0, typename _U1, typename _U2>
    operator Triple<_U0, _U1, _U2>() const {
      return {[&]() -> _U0 {
                if constexpr (std::is_same_v<A, std::any>) {
                  return crane_any_cast<_U0>(a0);
                } else {
                  if constexpr (std::is_constructible_v<_U0, const A &>) {
                    return _U0(a0);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }
              }(),
              [&]() -> _U1 {
                if constexpr (std::is_same_v<B, std::any>) {
                  return crane_any_cast<_U1>(a1);
                } else {
                  if constexpr (std::is_constructible_v<_U1, const B &>) {
                    return _U1(a1);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }
              }(),
              [&]() -> _U2 {
                if constexpr (std::is_same_v<C, std::any>) {
                  return crane_any_cast<_U2>(a2);
                } else {
                  if constexpr (std::is_constructible_v<_U2, const C &>) {
                    return _U2(a2);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }
              }()};
    }

    // CREATORS
    static Triple<A, B, C> mktriple(A a0, B a1, C a2) {
      return {std::move(a0), std::move(a1), std::move(a2)};
    }
  };

  template <typename T1, typename T2, typename T3, typename T4, typename F0>
    requires std::is_invocable_r_v<T4, F0 &, T1 &, T2 &, T3 &>
  static T4 Triple_rect(F0 &&f, const Triple<T1, T2, T3> &t) {
    const auto &[a0, a1, a2] = t;
    return f(a0, a1, a2);
  }

  template <typename T1, typename T2, typename T3, typename T4, typename F0>
    requires std::is_invocable_r_v<T4, F0 &, T1 &, T2 &, T3 &>
  static T4 Triple_rec(F0 &&f, const Triple<T1, T2, T3> &t) {
    const auto &[a0, a1, a2] = t;
    return f(a0, a1, a2);
  }

  static uint64_t sum_triple(const Triple<uint64_t, uint64_t, uint64_t> &t);

  template <typename T1, typename T2, typename T3>
  static Triple<T2, T3, T1> rotate_triple(const Triple<T1, T2, T3> &t) {
    const auto &[a0, a1, a2] = t;
    return Triple<T2, T3, T1>::mktriple(a1, a2, a0);
  }

  static inline const uint64_t test1 =
      sum_triple(Triple<uint64_t, uint64_t, uint64_t>::mktriple(
          UINT64_C(1), UINT64_C(2), UINT64_C(3)));
  static inline const Triple<bool, uint64_t, uint64_t> test2 =
      rotate_triple<uint64_t, bool, uint64_t>(
          Triple<uint64_t, bool, uint64_t>::mktriple(UINT64_C(10), true,
                                                     UINT64_C(20)));
};

#endif // INCLUDED_TODO_IOTA_COMPLEX_PATTERN
