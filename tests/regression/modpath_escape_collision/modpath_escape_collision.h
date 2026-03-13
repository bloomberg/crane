#ifndef INCLUDED_MODPATH_ESCAPE_COLLISION
#define INCLUDED_MODPATH_ESCAPE_COLLISION

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

struct ModpathEscapeCollision {
  struct A {
    struct Token_ {
      __attribute__((pure)) static unsigned int f(const unsigned int n);
    };
  };

  struct B {
    struct Token_ {
      __attribute__((pure)) static unsigned int g(const unsigned int n);
    };
  };

  static inline const unsigned int t = (A::Token_::f(0u) + B::Token_::g(0u));
};

#endif // INCLUDED_MODPATH_ESCAPE_COLLISION
