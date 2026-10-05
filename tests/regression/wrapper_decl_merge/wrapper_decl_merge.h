#ifndef INCLUDED_WRAPPER_DECL_MERGE
#define INCLUDED_WRAPPER_DECL_MERGE

#include <cstdint>

struct WrapperDeclMerge {
  struct A {
    struct Nat {
      static uint64_t fa(uint64_t n);
    };
  };

  struct B {
    struct Nat {
      static uint64_t fb(uint64_t n);
    };
  };

  static constexpr uint64_t x = UINT64_C(4);
  static constexpr uint64_t y = UINT64_C(5);
};

#endif // INCLUDED_WRAPPER_DECL_MERGE
