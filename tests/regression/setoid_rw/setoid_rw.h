#ifndef INCLUDED_SETOID_RW
#define INCLUDED_SETOID_RW

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

struct SetoidRw {
  __attribute__((pure)) static unsigned int mod3(const unsigned int n);
  __attribute__((pure)) static unsigned int classify_mod3(const unsigned int n);
  __attribute__((pure)) static unsigned int add_mod3(const unsigned int x,
                                                     const unsigned int y);
  static inline const unsigned int test_mod3_0 = mod3(0u);
  static inline const unsigned int test_mod3_5 = mod3(5u);
  static inline const unsigned int test_mod3_9 = mod3(9u);
  static inline const unsigned int test_classify_6 = classify_mod3(6u);
  static inline const unsigned int test_classify_7 = classify_mod3(7u);
  static inline const unsigned int test_add_mod3 = add_mod3(5u, 7u);
};

#endif // INCLUDED_SETOID_RW
