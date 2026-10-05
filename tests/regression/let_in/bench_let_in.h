#ifndef INCLUDED_BENCH_LET_IN
#define INCLUDED_BENCH_LET_IN

#include "crane_fn.h"
#include "obj.h"
#include <cstdint>
#include <type_traits>
#include <utility>
#include <variant>

struct BenchLetIn {
  template <typename A, typename B> struct pair {
    // DATA
    A a0;
    B a1;

    // ACCESSORS
    pair<A, B> clone() const { return {a0, a1}; }

    template <typename CraneU0, typename CraneU1>
      requires crane_convertible<CraneU0, const A &> &&
               crane_convertible<CraneU1, const B &>
    operator pair<CraneU0, CraneU1>() const {
      return {crane_convert<CraneU0>(a0), crane_convert<CraneU1>(a1)};
    }

    // CREATORS
    static pair<A, B> pair0(A a0, B a1) {
      return {std::move(a0), std::move(a1)};
    }

    template <typename T1, typename F0> T1 pair_rec(F0 &&f) const {
      return this->template pair_rect<T1>(f);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, const A &, const B &>
    T1 pair_rect(F0 &&f) const {
      const auto &[a0, a1] = *this;
      return f(a0, a1);
    }
  };

  static uint64_t swap_snd(uint64_t a, uint64_t b);
  static uint64_t add_via_pair(uint64_t a, uint64_t b);
  static uint64_t nested_swap(uint64_t a, uint64_t b, uint64_t c, uint64_t d);
  static uint64_t sum_via_pairs(uint64_t n);

  template <typename A, typename B, typename C> struct triple {
    // DATA
    A a0;
    B a1;
    C a2;

    // ACCESSORS
    triple<A, B, C> clone() const { return {a0, a1, a2}; }

    template <typename CraneU0, typename CraneU1, typename CraneU2>
      requires crane_convertible<CraneU0, const A &> &&
               crane_convertible<CraneU1, const B &> &&
               crane_convertible<CraneU2, const C &>
    operator triple<CraneU0, CraneU1, CraneU2>() const {
      return {crane_convert<CraneU0>(a0), crane_convert<CraneU1>(a1),
              crane_convert<CraneU2>(a2)};
    }

    // CREATORS
    static triple<A, B, C> triple0(A a0, B a1, C a2) {
      return {std::move(a0), std::move(a1), std::move(a2)};
    }

    template <typename T1, typename F0> T1 triple_rec(F0 &&f) const {
      return this->template triple_rect<T1>(f);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, const A &, const B &, const C &>
    T1 triple_rect(F0 &&f) const {
      const auto &[a0, a1, a2] = *this;
      return f(a0, a1, a2);
    }
  };

  static uint64_t mid3(uint64_t a, uint64_t b, uint64_t c);
  static uint64_t sum3(uint64_t a, uint64_t b, uint64_t c);
  static uint64_t chain_pairs(uint64_t a, uint64_t b, uint64_t c);
  static constexpr uint64_t test_swap = UINT64_C(4);
  static constexpr uint64_t test_add = UINT64_C(7);
  static constexpr uint64_t test_nested = UINT64_C(5);
  static constexpr uint64_t test_sum_pairs = UINT64_C(15);
  static constexpr uint64_t test_mid3 = UINT64_C(2);
  static constexpr uint64_t test_sum3 = UINT64_C(6);
  static constexpr uint64_t test_chain = UINT64_C(4);
};

#endif // INCLUDED_BENCH_LET_IN
