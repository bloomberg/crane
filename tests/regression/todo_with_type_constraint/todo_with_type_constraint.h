#ifndef INCLUDED_TODO_WITH_TYPE_CONSTRAINT
#define INCLUDED_TODO_WITH_TYPE_CONSTRAINT

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

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
concept NAT_BASE = BASE<M>;

struct TodoWithTypeConstraint {
  struct NatBase {
    using t = unsigned int;
    static inline const unsigned int zero = 0u;
    __attribute__((pure)) static unsigned int bump(const unsigned int n);
  };

  template <NAT_BASE X> struct UseNat {
    static const unsigned int &twice() {
      static const unsigned int v = X::bump(X::bump(X::zero));
      return v;
    }
  };

  using Applied = UseNat<NatBase>;
  static inline const unsigned int test_twice = Applied::twice();
};

#endif // INCLUDED_TODO_WITH_TYPE_CONSTRAINT
