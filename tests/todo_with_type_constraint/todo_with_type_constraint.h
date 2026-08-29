#ifndef INCLUDED_TODO_WITH_TYPE_CONSTRAINT
#define INCLUDED_TODO_WITH_TYPE_CONSTRAINT

#include <concepts>

template <typename M>
concept BASE = requires {
  typename M::t;
  requires(
      requires {
        { M::zero } -> std::convertible_to<typename M::t>;
      } ||
      requires {
        { M::zero() } -> std::convertible_to<typename M::t>;
      });
  { M::bump(std::declval<typename M::t>()) } -> std::same_as<typename M::t>;
};
template <typename M>
concept NAT_BASE = BASE<M> && std::same_as<typename M::t, uint64_t>;

struct TodoWithTypeConstraint {
  struct NatBase {
    using t = uint64_t;
    static inline const uint64_t zero = UINT64_C(0);
    static uint64_t bump(uint64_t n);
  };

  template <NAT_BASE X> struct UseNat {
    static const uint64_t &twice() {
      static const uint64_t v = X::bump(X::bump(X::zero));
      return v;
    }
  };

  using Applied = UseNat<NatBase>;
  static inline const uint64_t test_twice = Applied::twice();
};

#endif // INCLUDED_TODO_WITH_TYPE_CONSTRAINT
