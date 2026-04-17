#ifndef INCLUDED_TODO_WITH_MODULE_CONSTRAINT
#define INCLUDED_TODO_WITH_MODULE_CONSTRAINT

#include <concepts>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

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
    using t = unsigned int;
    static inline const unsigned int zero = 0u;
  };

  struct NatOuter {
    using Inner = NatInner;
    __attribute__((pure)) static Inner::t step(const unsigned int n);
  };

  template <OUTER_NAT X> struct UseNat {
    static const unsigned int &twice() {
      static const unsigned int v = X::step(X::step(X::Inner::zero));
      return v;
    }
  };

  using Applied = UseNat<NatOuter>;
  static inline const unsigned int test_twice = Applied::twice();
};

#endif // INCLUDED_TODO_WITH_MODULE_CONSTRAINT
