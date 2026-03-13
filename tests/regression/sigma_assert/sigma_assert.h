#ifndef INCLUDED_SIGMA_ASSERT
#define INCLUDED_SIGMA_ASSERT

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

struct PeanoNat {
  __attribute__((pure)) static unsigned int pred(const unsigned int n);
  __attribute__((pure)) static unsigned int div2(const unsigned int n);
};

struct SigmaAssert {
  __attribute__((pure)) static unsigned int safe_pred(const unsigned int n);
  __attribute__((pure)) static unsigned int safe_div2(const unsigned int n);
  static inline const unsigned int test_pred = safe_pred(5u);
  static inline const unsigned int test_div2 = safe_div2(4u);
};

#endif // INCLUDED_SIGMA_ASSERT
