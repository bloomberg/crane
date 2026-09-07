#ifndef INCLUDED_NESTED_MODULE_TYPE_CONCEPT
#define INCLUDED_NESTED_MODULE_TYPE_CONCEPT

#include <concepts>

/// A module type declared inside another module yields no concept at all: the
/// enclosing module is emitted as an empty struct Defs, and the functor
/// constrained by it names a concept that was never declared.
struct NestedModuleTypeConcept {
  struct Defs {};

  template <S X> struct F {
    static const typename X::t &get() {
      static const typename X::t v = X::d;
      return v;
    }
  };

  struct A {
    using t = uint64_t;
    static inline const t d = UINT64_C(1);
  };

  using FA = F<A>;
  static inline const uint64_t test = FA::get();
};

#endif // INCLUDED_NESTED_MODULE_TYPE_CONCEPT
