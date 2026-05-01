#ifndef INCLUDED_MODPATH_ESCAPE_COLLISION
#define INCLUDED_MODPATH_ESCAPE_COLLISION

#include <memory>
#include <optional>
#include <type_traits>

struct ModpathEscapeCollision {
  struct A {
    struct Token_ {
      static unsigned int f(const unsigned int n);
    };
  };

  struct B {
    struct Token_ {
      static unsigned int g(const unsigned int n);
    };
  };

  static inline const unsigned int t = (A::Token_::f(0u) + B::Token_::g(0u));
};

#endif // INCLUDED_MODPATH_ESCAPE_COLLISION
