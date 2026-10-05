#ifndef INCLUDED_TODO_ETA_EXPANSION_TAXIOM
#define INCLUDED_TODO_ETA_EXPANSION_TAXIOM

#include "crane_fn.h"
#include "obj.h"
#include <cstdint>
#include <type_traits>
#include <utility>
#include <variant>

struct TodoEtaExpansionTaxiom {
  template <typename A, typename B> struct Pair {
    // DATA
    A a0;
    B a1;

    // ACCESSORS
    Pair<A, B> clone() const { return {a0, a1}; }

    template <typename CraneU0, typename CraneU1>
      requires crane_convertible<CraneU0, const A &> &&
               crane_convertible<CraneU1, const B &>
    operator Pair<CraneU0, CraneU1>() const {
      return {crane_convert<CraneU0>(a0), crane_convert<CraneU1>(a1)};
    }

    // CREATORS
    static Pair<A, B> mkpair(A a0, B a1) {
      return {std::move(a0), std::move(a1)};
    }
  };

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, const T1 &, const T2 &>
  static T3 Pair_rect(F0 &&f, const Pair<T1, T2> &p) {
    const auto &[a0, a1] = p;
    return f(a0, a1);
  }

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, const T1 &, const T2 &>
  static T3 Pair_rec(F0 &&f, const Pair<T1, T2> &p) {
    const auto &[a0, a1] = p;
    return f(a0, a1);
  }

  template <typename T1, typename T2>
  static Pair<T2, T1> swap_pair(const Pair<T1, T2> &p) {
    const auto &[a0, a1] = p;
    return Pair<T2, T1>::mkpair(a1, a0);
  }

  template <typename T1, typename T2>
  static T1 fst_pair(const Pair<T1, T2> &p) {
    const auto &[a0, a1] = p;
    return a0;
  }

  static inline const Pair<bool, uint64_t> test_swap =
      swap_pair<uint64_t, bool>(
          Pair<uint64_t, bool>::mkpair(UINT64_C(3), true));

  static constexpr uint64_t test_fst = UINT64_C(42);
};

#endif // INCLUDED_TODO_ETA_EXPANSION_TAXIOM
