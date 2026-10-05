#ifndef INCLUDED_MODPATH_ESCAPE_COLLISION
#define INCLUDED_MODPATH_ESCAPE_COLLISION

#include <cstdint>

struct ModpathEscapeCollision {
  struct A {
    struct Token_ {
      static uint64_t f(uint64_t n);
    };
  };

  struct B {
    struct Token_ {
      static uint64_t g(uint64_t n);
    };
  };

  static constexpr uint64_t t = UINT64_C(1);
};

#endif // INCLUDED_MODPATH_ESCAPE_COLLISION
