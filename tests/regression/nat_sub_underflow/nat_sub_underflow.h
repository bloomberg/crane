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

struct NatSubUnderflow {
  static unsigned int value_(const unsigned int n);

  static unsigned int value_0(const unsigned int n);

  static inline const unsigned int t =
      (value_((0 + 1)) + value_0(((0 + 1) + 1)));
};
