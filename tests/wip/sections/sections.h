#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Sections {
  static unsigned int add_n(const unsigned int, const unsigned int);

  static unsigned int mul_n(const unsigned int, const unsigned int);

  static unsigned int add_five(const unsigned int);

  static unsigned int mul_three(const unsigned int);

  static unsigned int sum_ab(const unsigned int, const unsigned int);

  static unsigned int prod_ab(const unsigned int, const unsigned int);

  static unsigned int use_inner(const unsigned int a);

  static inline const unsigned int final_use = use_inner(5u);

  template <typename T1> static T1 identity(const T1 x) { return x; }

  template <typename T1> static T1 const(const T1 x, const T1 _x) { return x; }

  static inline const unsigned int test_add = add_five(2u);

  static inline const unsigned int test_mul = mul_three(4u);

  static inline const unsigned int test_nested = final_use;

  static inline const unsigned int test_id = identity<unsigned int>(7u);

  static inline const unsigned int test_const = const<unsigned int>(3u, 9u);
};
