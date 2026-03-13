#ifndef INCLUDED_ESCAPE_COLLISION
#define INCLUDED_ESCAPE_COLLISION

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

struct EscapeCollision {
  __attribute__((pure)) static unsigned int double_(const unsigned int n);
  __attribute__((pure)) static unsigned int double_0(const unsigned int n);
  static inline const unsigned int t = (double_(1u) + double_0(2u));
};

#endif // INCLUDED_ESCAPE_COLLISION
