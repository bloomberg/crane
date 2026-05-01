#ifndef INCLUDED_WRAPPER_DECL_MERGE
#define INCLUDED_WRAPPER_DECL_MERGE

#include <memory>
#include <optional>
#include <type_traits>

struct WrapperDeclMerge {
  struct A {
    struct Nat {
      static unsigned int fa(const unsigned int n);
    };
  };

  struct B {
    struct Nat {
      static unsigned int fb(const unsigned int n);
    };
  };

  static inline const unsigned int x = A::Nat::fa(4u);
  static inline const unsigned int y = B::Nat::fb(4u);
};

#endif // INCLUDED_WRAPPER_DECL_MERGE
