#ifndef INCLUDED_TODO_GENERALIZABLE_APPROX
#define INCLUDED_TODO_GENERALIZABLE_APPROX

#include <type_traits>

struct TodoGeneralizableApprox {
  template <typename F0>
    requires std::is_invocable_r_v<unsigned int, F0 &, unsigned int &>
  static unsigned int apply_twice(F0 &&f, unsigned int x) {
    return f(f(x));
  }

  static unsigned int double_then_add(unsigned int x);
  static inline const unsigned int test1 =
      apply_twice([](unsigned int n) { return (n + 1u); }, 5u);
  static inline const unsigned int test2 = double_then_add(3u);
};

#endif // INCLUDED_TODO_GENERALIZABLE_APPROX
