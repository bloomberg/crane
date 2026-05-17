#ifndef INCLUDED_LAMBDA
#define INCLUDED_LAMBDA

#include <type_traits>

struct Lambda {
  static unsigned int simple_lambda(unsigned int x);
  static unsigned int multi_arg(unsigned int _x0, unsigned int _x1);
  static unsigned int nested_lambda(unsigned int x, unsigned int y,
                                    unsigned int z);
  static unsigned int make_adder(unsigned int _x0, unsigned int _x1);
  static inline const unsigned int with_let = []() {
    unsigned int x = 5u;
    return (x * 2u);
  }();

  template <typename F0>
    requires std::is_invocable_r_v<unsigned int, F0 &, unsigned int &>
  static unsigned int apply_fn(F0 &&f, unsigned int _x0) {
    return f(_x0);
  }

  static inline const unsigned int use_apply =
      apply_fn([](unsigned int x) { return (x + 1u); }, 5u);
  static inline const unsigned int test_simple = simple_lambda(5u);
  static inline const unsigned int test_multi = multi_arg(3u, 4u);
  static inline const unsigned int test_nested = nested_lambda(1u, 2u, 3u);
  static inline const unsigned int test_adder = make_adder(3u, 5u);
  static inline const unsigned int test_let = with_let;
  static inline const unsigned int test_apply = use_apply;
};

#endif // INCLUDED_LAMBDA
