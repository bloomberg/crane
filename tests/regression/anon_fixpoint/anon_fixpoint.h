#include <algorithm>
#include <any>
#include <functional>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct AnonFixpoint {
  static unsigned int sum_to(const unsigned int n);

  static unsigned int factorial(const unsigned int m);

  static unsigned int double_sum(const unsigned int m);

  static unsigned int gcd(const unsigned int a, const unsigned int b);

  static inline const unsigned int test_sum_5 = sum_to(5u);

  static inline const unsigned int test_sum_0 = sum_to(0u);

  static inline const unsigned int test_fact_5 = factorial(5u);

  static inline const unsigned int test_fact_0 = factorial(0u);

  static inline const unsigned int test_double = double_sum(3u);

  static inline const unsigned int test_gcd = gcd((4u * 3u), (2u * 3u));
};
