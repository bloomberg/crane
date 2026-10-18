#ifndef INCLUDED_ASSERTION_HELD_THROUGH_STRUCTS
#define INCLUDED_ASSERTION_HELD_THROUGH_STRUCTS

#include <concepts>
#include <cstdint>
#include <utility>

struct AssertionHeldThroughStructs {
  using key = uint64_t;

  struct Mid {
    struct S {
      static uint64_t lookup(uint64_t k);
    };

    struct Inner {
      struct S2 {
        static uint64_t lookup(uint64_t k);
      };

      struct hk {
        static key getk(uint64_t n) { return n; }
      };
    };

    static inline const uint64_t run =
        ((S::lookup(UINT64_C(1)) + Inner::S2::lookup(UINT64_C(2))) +
         Inner::hk::getk(UINT64_C(3)));
  };
};

template <typename I, typename A>
concept HasK = requires {
  {
    I::getk(std::declval<A>())
  } -> std::convertible_to<AssertionHeldThroughStructs::key>;
};
template <typename M>
concept STORE = requires {
  {
    M::lookup(std::declval<AssertionHeldThroughStructs::key>())
  } -> std::same_as<uint64_t>;
};

static_assert(STORE<AssertionHeldThroughStructs::Mid::S>);
static_assert(STORE<AssertionHeldThroughStructs::Mid::Inner::S2>);
static_assert(HasK<AssertionHeldThroughStructs::Mid::Inner::hk, uint64_t>);

#endif // INCLUDED_ASSERTION_HELD_THROUGH_STRUCTS
