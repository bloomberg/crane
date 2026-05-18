#ifndef INCLUDED_TODO_NESTED_MODULE_TYPE
#define INCLUDED_TODO_NESTED_MODULE_TYPE

#include <concepts>

template <typename M>
concept INNER = requires {
  typename M::t;
  requires(
      requires {
        { M::zero } -> std::convertible_to<typename M::t>;
      } ||
      requires {
        { M::zero() } -> std::convertible_to<typename M::t>;
      });
};
template <typename M>
concept OUTER = requires {
  requires INNER<typename M::Inner>;
  {
    M::step(std::declval<typename M::Inner::t>())
  } -> std::same_as<typename M::Inner::t>;
};

struct TodoNestedModuleType {
  template <OUTER X> struct Make {
    static const typename X::Inner::t &twice() {
      static const typename X::Inner::t v = X::step(X::step(X::Inner::zero));
      return v;
    }
  };

  struct NatInner {
    using t = uint64_t;
    static inline const uint64_t zero = UINT64_C(0);
  };

  struct NatOuter {
    using Inner = NatInner;
    static Inner::t step(uint64_t n);
  };

  using UseNat = Make<NatOuter>;
  static inline const uint64_t test_twice = UseNat::twice();
};

#endif // INCLUDED_TODO_NESTED_MODULE_TYPE
