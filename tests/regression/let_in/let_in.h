#ifndef INCLUDED_LET_IN
#define INCLUDED_LET_IN

#include <type_traits>
#include <utility>
#include <variant>

struct LetIn {
  static inline const uint64_t simple_let = UINT64_C(5);
  static inline const uint64_t nested_let = UINT64_C(3);
  static inline const uint64_t let_with_add = []() {
    uint64_t x = UINT64_C(3);
    uint64_t y = UINT64_C(4);
    return (x + y);
  }();
  static inline const uint64_t shadowed_let = UINT64_C(3);
  static uint64_t let_in_fun(uint64_t n);
  static inline const uint64_t let_fun = []() {
    uint64_t x = UINT64_C(5);
    return (x + UINT64_C(1));
  }();

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

  static inline const uint64_t let_destruct = []() {
    pair<uint64_t, uint64_t> p =
        pair<uint64_t, uint64_t>::pair0(UINT64_C(3), UINT64_C(4));
    auto &[a0, a1] = p;
    return a0;
  }();
  static inline const uint64_t multi_let = []() {
    uint64_t a = UINT64_C(1);
    uint64_t b = UINT64_C(2);
    uint64_t c = UINT64_C(3);
    return (a + (b + c));
  }();
  static inline const uint64_t test_simple = simple_let;
  static inline const uint64_t test_nested = nested_let;
  static inline const uint64_t test_add = let_with_add;
  static inline const uint64_t test_shadow = shadowed_let;
  static inline const uint64_t test_fun_call = let_in_fun(UINT64_C(3));
  static inline const uint64_t test_let_fun = let_fun;
  static inline const uint64_t test_destruct = let_destruct;
  static inline const uint64_t test_multi = multi_let;
};

#endif // INCLUDED_LET_IN
