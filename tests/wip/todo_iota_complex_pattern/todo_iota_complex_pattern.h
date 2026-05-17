#ifndef INCLUDED_TODO_IOTA_COMPLEX_PATTERN
#define INCLUDED_TODO_IOTA_COMPLEX_PATTERN

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

  static unsigned int
  sum_triple(const Triple<unsigned int, unsigned int, unsigned int> &t);

  template <typename T1, typename T2, typename T3>
  static Triple<T2, T3, T1> rotate_triple(const Triple<T1, T2, T3> &t) {
    const auto &[a0, a1, a2] = t;
    return Triple<T2, T3, T1>::mktriple(a1, a2, a0);
  }

  static inline const unsigned int test1 = sum_triple(
      Triple<unsigned int, unsigned int, unsigned int>::mktriple(1u, 2u, 3u));
  static inline const Triple<bool, unsigned int, unsigned int> test2 =
      rotate_triple<unsigned int, bool, unsigned int>(
          Triple<unsigned int, bool, unsigned int>::mktriple(10u, true, 20u));
};

#endif // INCLUDED_TODO_IOTA_COMPLEX_PATTERN
