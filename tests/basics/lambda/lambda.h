#ifndef INCLUDED_LAMBDA
#define INCLUDED_LAMBDA

#include <type_traits>

struct Lambda {
  static uint64_t simple_lambda(uint64_t x);
  static uint64_t multi_arg(uint64_t _x0, uint64_t _x1);
  static uint64_t nested_lambda(uint64_t x, uint64_t y, uint64_t z);
  static uint64_t make_adder(uint64_t _x0, uint64_t _x1);
  static inline const uint64_t with_let = []() {
    uint64_t x = UINT64_C(5);
    return (x * UINT64_C(2));
  }();

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static uint64_t apply_fn(F0 &&f, uint64_t _x0) {
    return f(_x0);
  }

  static inline const uint64_t use_apply =
      apply_fn([](uint64_t x) { return (x + UINT64_C(1)); }, UINT64_C(5));
  static inline const uint64_t test_simple = simple_lambda(UINT64_C(5));
  static inline const uint64_t test_multi = multi_arg(UINT64_C(3), UINT64_C(4));
  static inline const uint64_t test_nested =
      nested_lambda(UINT64_C(1), UINT64_C(2), UINT64_C(3));
  static inline const uint64_t test_adder =
      make_adder(UINT64_C(3), UINT64_C(5));
  static inline const uint64_t test_let = with_let;
  static inline const uint64_t test_apply = use_apply;
};

#endif // INCLUDED_LAMBDA
