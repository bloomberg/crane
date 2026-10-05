#ifndef INCLUDED_CURRYING
#define INCLUDED_CURRYING

#include "crane_fn.h"
#include "obj.h"
#include <cstdint>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct Currying {
  static uint64_t add3(uint64_t a, uint64_t b, uint64_t c);
  static uint64_t add3_partial1(uint64_t x0_, uint64_t x1_);
  static uint64_t add3_partial2(uint64_t x0_);

  template <typename A, typename B> struct pair {
    // DATA
    A a0;
    B a1;

    // ACCESSORS
    pair<A, B> clone() const { return {a0, a1}; }

    template <typename CraneU0, typename CraneU1>
    operator pair<CraneU0, CraneU1>() const {
      return {[&]() -> CraneU0 {
                if constexpr (crane_convertible<CraneU0, const A &>) {
                  return crane_convert<CraneU0>(a0);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }(),
              [&]() -> CraneU1 {
                if constexpr (crane_convertible<CraneU1, const B &>) {
                  return crane_convert<CraneU1>(a1);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }()};
    }

    // CREATORS
    static pair<A, B> pair0(A a0, B a1) {
      return {std::move(a0), std::move(a1)};
    }
  };

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, const T1 &, const T2 &>
  static T3 pair_rect(F0 &&f, const pair<T1, T2> &p) {
    const auto &[a0, a1] = p;
    return f(a0, a1);
  }

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, const T1 &, const T2 &>
  static T3 pair_rec(F0 &&f, const pair<T1, T2> &p) {
    const auto &[a0, a1] = p;
    return f(a0, a1);
  }

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, pair<T1, T2>>
  static T3 curry(F0 &&f, const T1 &a, const T2 &b) {
    return f(pair<T1, T2>::pair0(a, b));
  }

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, const T1 &, const T2 &>
  static T3 uncurry(F0 &&f, const pair<T1, T2> &p) {
    const auto &[a0, a1] = p;
    return f(a0, a1);
  }

  static uint64_t pair_add(const pair<uint64_t, uint64_t> &p);
  static uint64_t curried_add(uint64_t x0_, uint64_t x1_);
  static uint64_t
  uncurried_add3(const pair<uint64_t, pair<uint64_t, uint64_t>> &p);

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, const T1 &, const T2 &>
  static T3 flip(F0 &&f, const T2 &b, const T1 &a) {
    return f(a, b);
  }

  static uint64_t sub(uint64_t x0_, uint64_t x1_);
  static uint64_t flipped_sub(uint64_t x0_, uint64_t x1_);
  static uint64_t add_base(uint64_t x0_, uint64_t x1_);
  static uint64_t add_ten(uint64_t x0_);
  static constexpr uint64_t test_add3 = UINT64_C(6);
  static constexpr uint64_t test_partial1 = UINT64_C(6);
  static constexpr uint64_t test_partial2 = UINT64_C(6);
  static constexpr uint64_t test_curried = UINT64_C(7);
  static constexpr uint64_t test_flip = UINT64_C(4);
  static constexpr uint64_t test_add_ten = UINT64_C(15);
};

#endif // INCLUDED_CURRYING
