#ifndef INCLUDED_BENCH_LET_IN
#define INCLUDED_BENCH_LET_IN

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

    // CREATORS
    static pair<A, B> pair0(A a0, B a1) {
      return {std::move(a0), std::move(a1)};
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &, B &>
    T1 pair_rec(F0 &&f) const {
      const auto &[a0, a1] = *this;
      return f(a0, a1);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &, B &>
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

    // CREATORS
    static triple<A, B, C> triple0(A a0, B a1, C a2) {
      return {std::move(a0), std::move(a1), std::move(a2)};
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &, B &, C &>
    T1 triple_rec(F0 &&f) const {
      const auto &[a0, a1, a2] = *this;
      return f(a0, a1, a2);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &, B &, C &>
    T1 triple_rect(F0 &&f) const {
      const auto &[a0, a1, a2] = *this;
      return f(a0, a1, a2);
    }
  };

  static uint64_t mid3(uint64_t a, uint64_t b, uint64_t c);
  static uint64_t sum3(uint64_t a, uint64_t b, uint64_t c);
  static uint64_t chain_pairs(uint64_t a, uint64_t b, uint64_t c);
  static inline const uint64_t test_swap = swap_snd(UINT64_C(3), UINT64_C(4));
  static inline const uint64_t test_add =
      add_via_pair(UINT64_C(3), UINT64_C(4));
  static inline const uint64_t test_nested =
      nested_swap(UINT64_C(1), UINT64_C(2), UINT64_C(3), UINT64_C(4));
  static inline const uint64_t test_sum_pairs = sum_via_pairs(UINT64_C(5));
  static inline const uint64_t test_mid3 =
      mid3(UINT64_C(1), UINT64_C(2), UINT64_C(3));
  static inline const uint64_t test_sum3 =
      sum3(UINT64_C(1), UINT64_C(2), UINT64_C(3));
  static inline const uint64_t test_chain =
      chain_pairs(UINT64_C(1), UINT64_C(2), UINT64_C(3));
};

#endif // INCLUDED_BENCH_LET_IN
