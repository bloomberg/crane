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
      const auto &_sv = *this;
      const auto &[a0, a1] = _sv;
      return f(a0, a1);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &, B &>
    T1 pair_rect(F0 &&f) const {
      const auto &_sv = *this;
      const auto &[a0, a1] = _sv;
      return f(a0, a1);
    }
  };

  static unsigned int swap_snd(unsigned int a, unsigned int b);
  static unsigned int add_via_pair(unsigned int a, unsigned int b);
  static unsigned int nested_swap(unsigned int a, unsigned int b,
                                  unsigned int c, unsigned int d);
  static unsigned int sum_via_pairs(unsigned int n);

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
      const auto &_sv = *this;
      const auto &[a0, a1, a2] = _sv;
      return f(a0, a1, a2);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &, B &, C &>
    T1 triple_rect(F0 &&f) const {
      const auto &_sv = *this;
      const auto &[a0, a1, a2] = _sv;
      return f(a0, a1, a2);
    }
  };

  static unsigned int mid3(unsigned int a, unsigned int b, unsigned int c);
  static unsigned int sum3(unsigned int a, unsigned int b, unsigned int c);
  static unsigned int chain_pairs(unsigned int a, unsigned int b,
                                  unsigned int c);
  static inline const unsigned int test_swap = swap_snd(3u, 4u);
  static inline const unsigned int test_add = add_via_pair(3u, 4u);
  static inline const unsigned int test_nested = nested_swap(1u, 2u, 3u, 4u);
  static inline const unsigned int test_sum_pairs = sum_via_pairs(5u);
  static inline const unsigned int test_mid3 = mid3(1u, 2u, 3u);
  static inline const unsigned int test_sum3 = sum3(1u, 2u, 3u);
  static inline const unsigned int test_chain = chain_pairs(1u, 2u, 3u);
};

#endif // INCLUDED_BENCH_LET_IN
