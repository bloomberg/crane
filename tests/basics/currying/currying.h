#ifndef INCLUDED_CURRYING
#define INCLUDED_CURRYING

#include <type_traits>
#include <utility>
#include <variant>

struct Currying {
  static uint64_t add3(uint64_t a, uint64_t b, uint64_t c);
  static uint64_t add3_partial1(uint64_t _x0, uint64_t _x1);
  static uint64_t add3_partial2(uint64_t _x0);

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
  };

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T1 &, T2 &>
  static T3 pair_rect(F0 &&f, const pair<T1, T2> &p) {
    const auto &[a0, a1] = p;
    return f(a0, a1);
  }

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T1 &, T2 &>
  static T3 pair_rec(F0 &&f, const pair<T1, T2> &p) {
    const auto &[a0, a1] = p;
    return f(a0, a1);
  }

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, pair<T1, T2> &>
  static T3 curry(F0 &&f, T1 a, T2 b) {
    return f(pair<T1, T2>::pair0(a, b));
  }

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T1 &, T2 &>
  static T3 uncurry(F0 &&f, const pair<T1, T2> &p) {
    const auto &[a0, a1] = p;
    return f(a0, a1);
  }

  static uint64_t pair_add(const pair<uint64_t, uint64_t> &p);
  static uint64_t curried_add(uint64_t _x0, uint64_t _x1);
  static uint64_t
  uncurried_add3(const pair<uint64_t, pair<uint64_t, uint64_t>> &p);

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T1 &, T2 &>
  static T3 flip(F0 &&f, const T2 &b, const T1 &a) {
    return f(a, b);
  }

  static uint64_t sub(uint64_t _x0, uint64_t _x1);
  static uint64_t flipped_sub(uint64_t _x0, uint64_t _x1);
  static uint64_t add_base(uint64_t _x0, uint64_t _x1);
  static uint64_t add_ten(uint64_t _x0);
  static inline const uint64_t test_add3 =
      add3(UINT64_C(1), UINT64_C(2), UINT64_C(3));
  static inline const uint64_t test_partial1 =
      add3_partial1(UINT64_C(2), UINT64_C(3));
  static inline const uint64_t test_partial2 = add3_partial2(UINT64_C(3));
  static inline const uint64_t test_curried =
      curried_add(UINT64_C(3), UINT64_C(4));
  static inline const uint64_t test_flip =
      flipped_sub(UINT64_C(3), UINT64_C(7));
  static inline const uint64_t test_add_ten = add_ten(UINT64_C(5));
};

#endif // INCLUDED_CURRYING
