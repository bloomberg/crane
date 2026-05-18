#ifndef INCLUDED_MODPATH_ESCAPE_COLLISION
#define INCLUDED_MODPATH_ESCAPE_COLLISION

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

  static inline const uint64_t t =
      (A::Token_::f(UINT64_C(0)) + B::Token_::g(UINT64_C(0)));
};

#endif // INCLUDED_MODPATH_ESCAPE_COLLISION
