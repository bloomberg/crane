#ifndef INCLUDED_MODPATH_ESCAPE_COLLISION
#define INCLUDED_MODPATH_ESCAPE_COLLISION

#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct ModpathEscapeCollision {
  struct A {
    struct Token_ {
      static unsigned int f(unsigned int n);
    };
  };

  struct B {
    struct Token_ {
      static unsigned int g(unsigned int n);
    };
  };

  static inline const unsigned int t = (A::Token_::f(0u) + B::Token_::g(0u));
};

#endif // INCLUDED_MODPATH_ESCAPE_COLLISION
