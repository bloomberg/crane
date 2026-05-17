#ifndef INCLUDED_CURRYING
#define INCLUDED_CURRYING

#include <type_traits>
#include <utility>
#include <variant>

struct Currying {
  static unsigned int add3(unsigned int a, unsigned int b, unsigned int c);
  static unsigned int add3_partial1(unsigned int _x0, unsigned int _x1);
  static unsigned int add3_partial2(unsigned int _x0);

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

  static unsigned int pair_add(const pair<unsigned int, unsigned int> &p);
  static unsigned int curried_add(unsigned int _x0, unsigned int _x1);
  static unsigned int
  uncurried_add3(const pair<unsigned int, pair<unsigned int, unsigned int>> &p);

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, T1 &, T2 &>
  static T3 flip(F0 &&f, const T2 &b, const T1 &a) {
    return f(a, b);
  }

  static unsigned int sub(unsigned int _x0, unsigned int _x1);
  static unsigned int flipped_sub(unsigned int _x0, unsigned int _x1);
  static unsigned int add_base(unsigned int _x0, unsigned int _x1);
  static unsigned int add_ten(unsigned int _x0);
  static inline const unsigned int test_add3 = add3(1u, 2u, 3u);
  static inline const unsigned int test_partial1 = add3_partial1(2u, 3u);
  static inline const unsigned int test_partial2 = add3_partial2(3u);
  static inline const unsigned int test_curried = curried_add(3u, 4u);
  static inline const unsigned int test_flip = flipped_sub(3u, 7u);
  static inline const unsigned int test_add_ten = add_ten(5u);
};

#endif // INCLUDED_CURRYING
