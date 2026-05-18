#ifndef INCLUDED_FUNC_ONLY_SUBMODULE_AB
#define INCLUDED_FUNC_ONLY_SUBMODULE_AB

struct FuncOnlySubmoduleAb {
  struct Root {
    struct A {
      static uint64_t inc(uint64_t n);
    };

    struct B {
      static uint64_t dec(uint64_t _x0);
    };
  };

  static inline const uint64_t t = Root::A::inc(Root::B::dec(UINT64_C(3)));
};

#endif // INCLUDED_FUNC_ONLY_SUBMODULE_AB
