#ifndef INCLUDED_WRAPPER_DECL_MERGE
#define INCLUDED_WRAPPER_DECL_MERGE

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

  static inline const uint64_t x = A::Nat::fa(UINT64_C(4));
  static inline const uint64_t y = B::Nat::fb(UINT64_C(4));
};

#endif // INCLUDED_WRAPPER_DECL_MERGE
