#ifndef INCLUDED_TODO_GENERALIZABLE_APPROX
#define INCLUDED_TODO_GENERALIZABLE_APPROX

#include <cstdint>
#include <type_traits>

struct TodoGeneralizableApprox {
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t> &&
             std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static uint64_t apply_twice(F0 &&f, uint64_t x) {
    return f(f(x));
  }

  static uint64_t double_then_add(uint64_t x);
  static constexpr uint64_t test1 = UINT64_C(7);
  static constexpr uint64_t test2 = UINT64_C(7);
};

#endif // INCLUDED_TODO_GENERALIZABLE_APPROX
