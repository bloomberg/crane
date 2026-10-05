#ifndef INCLUDED_LAMBDA
#define INCLUDED_LAMBDA

#include <cstdint>
#include <type_traits>

struct Lambda {
  static uint64_t simple_lambda(uint64_t x);
  static uint64_t multi_arg(uint64_t x0_, uint64_t x1_);
  static uint64_t nested_lambda(uint64_t x, uint64_t y, uint64_t z);
  static uint64_t make_adder(uint64_t x0_, uint64_t x1_);
  static constexpr uint64_t with_let = UINT64_C(10);

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static uint64_t apply_fn(F0 &&f, uint64_t x0_) {
    return f(x0_);
  }

  static constexpr uint64_t use_apply = UINT64_C(6);
  static constexpr uint64_t test_simple = UINT64_C(5);
  static constexpr uint64_t test_multi = UINT64_C(7);
  static constexpr uint64_t test_nested = UINT64_C(6);
  static constexpr uint64_t test_adder = UINT64_C(8);
  static constexpr uint64_t test_let = UINT64_C(10);
  static constexpr uint64_t test_apply = UINT64_C(6);
};

#endif // INCLUDED_LAMBDA
