#ifndef INCLUDED_TODO_GENERALIZABLE_APPROX
#define INCLUDED_TODO_GENERALIZABLE_APPROX

#include <type_traits>

struct TodoGeneralizableApprox {
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static uint64_t apply_twice(F0 &&f, uint64_t x) {
    return f(f(x));
  }

  static uint64_t double_then_add(uint64_t x);
  static inline const uint64_t test1 =
      apply_twice([](uint64_t n) { return (n + UINT64_C(1)); }, UINT64_C(5));
  static inline const uint64_t test2 = double_then_add(UINT64_C(3));
};

#endif // INCLUDED_TODO_GENERALIZABLE_APPROX
