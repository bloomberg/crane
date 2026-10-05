#ifndef INCLUDED_LET_IN
#define INCLUDED_LET_IN

#include "crane_fn.h"
#include "obj.h"
#include <cstdint>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct LetIn {
  static constexpr uint64_t simple_let = UINT64_C(5);
  static constexpr uint64_t nested_let = UINT64_C(3);
  static constexpr uint64_t let_with_add = UINT64_C(7);
  static constexpr uint64_t shadowed_let = UINT64_C(3);
  static uint64_t let_in_fun(uint64_t n);
  static constexpr uint64_t let_fun = UINT64_C(6);

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
  static T3 pair_rec(F0 &&f, const pair<T1, T2> &p) {
    return pair_rect<T1, T2, T3>(f, p);
  }

  static constexpr uint64_t let_destruct = UINT64_C(3);
  static constexpr uint64_t multi_let = UINT64_C(6);
  static constexpr uint64_t test_simple = UINT64_C(5);
  static constexpr uint64_t test_nested = UINT64_C(3);
  static constexpr uint64_t test_add = UINT64_C(7);
  static constexpr uint64_t test_shadow = UINT64_C(3);
  static constexpr uint64_t test_fun_call = UINT64_C(6);
  static constexpr uint64_t test_let_fun = UINT64_C(6);
  static constexpr uint64_t test_destruct = UINT64_C(3);
  static constexpr uint64_t test_multi = UINT64_C(6);
};

#endif // INCLUDED_LET_IN
