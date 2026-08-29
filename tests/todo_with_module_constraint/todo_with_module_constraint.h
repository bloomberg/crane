#ifndef INCLUDED_TODO_WITH_MODULE_CONSTRAINT
#define INCLUDED_TODO_WITH_MODULE_CONSTRAINT

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
template <typename M>
concept OUTER_NAT = OUTER<M>;

struct TodoWithModuleConstraint {
  struct NatInner {
    using t = uint64_t;
    static inline const uint64_t zero = UINT64_C(0);
  };

  struct NatOuter {
    using Inner = NatInner;
    static Inner::t step(uint64_t n);
  };

  template <OUTER_NAT X> struct UseNat {
    static const uint64_t &twice() {
      static const uint64_t v = X::step(X::step(X::Inner::zero));
      return v;
    }
  };

  using Applied = UseNat<NatOuter>;
  static inline const uint64_t test_twice = Applied::twice();
};

#endif // INCLUDED_TODO_WITH_MODULE_CONSTRAINT
