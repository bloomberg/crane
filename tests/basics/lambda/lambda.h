#ifndef INCLUDED_LAMBDA
#define INCLUDED_LAMBDA

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Lambda {
  __attribute__((pure)) static unsigned int simple_lambda(const unsigned int x);
  __attribute__((pure)) static unsigned int multi_arg(const unsigned int _x0,
                                                      const unsigned int _x1);
  __attribute__((pure)) static unsigned int nested_lambda(const unsigned int x,
                                                          const unsigned int y,
                                                          const unsigned int z);
  __attribute__((pure)) static unsigned int make_adder(const unsigned int _x0,
                                                       const unsigned int _x1);
  static inline const unsigned int with_let = [](void) {
    unsigned int x = 5u;
    return (std::move(x) * 2u);
  }();

  template <MapsTo<unsigned int, unsigned int> F0>
  __attribute__((pure)) static unsigned int apply_fn(F0 &&f,
                                                     const unsigned int _x0) {
    return f(std::move(_x0));
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
