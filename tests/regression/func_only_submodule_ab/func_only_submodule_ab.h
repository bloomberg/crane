#ifndef INCLUDED_FUNC_ONLY_SUBMODULE_AB
#define INCLUDED_FUNC_ONLY_SUBMODULE_AB

struct FuncOnlySubmoduleAb {
  struct Root {
    struct A {
      static unsigned int inc(unsigned int n);
    };

    struct B {
      static unsigned int dec(unsigned int _x0);
    };
  };

  static inline const unsigned int t = Root::A::inc(Root::B::dec(3u));
};

#endif // INCLUDED_FUNC_ONLY_SUBMODULE_AB
