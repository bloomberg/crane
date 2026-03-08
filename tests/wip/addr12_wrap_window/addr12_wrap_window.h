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

struct Nat {
  static unsigned int pow(const unsigned int n, const unsigned int m);
};

struct Addr12WrapWindow {
  static unsigned int addr12_of_nat(const unsigned int n);

  static inline const unsigned int t = addr12_of_nat((Nat::pow(2u, 12u) + 5u));
};
