#ifndef INCLUDED_NESTED_CLASS_CONCEPT_SCOPE
#define INCLUDED_NESTED_CLASS_CONCEPT_SCOPE

#include <concepts>
#include <utility>

template <typename I, typename A>
concept C = requires {
  { I::m(std::declval<A>()) } -> std::convertible_to<uint64_t>;
};

/// A class declared inside a submodule has its concept hoisted to file scope,
/// because a C++ concept cannot be a class member.  The static_assert
/// checking the instance is not told about the hoist and still spells the
/// concept with the submodule path, Outer::Inner::C.
struct NestedClassConceptScope {
  struct Outer {
    struct Inner {};
  };

  struct IN {
    static uint64_t m(uint64_t n) { return n; }
  };

  static_assert(C<IN, uint64_t>);
  static inline const uint64_t test = IN::m(UINT64_C(5));
};

#endif // INCLUDED_NESTED_CLASS_CONCEPT_SCOPE
