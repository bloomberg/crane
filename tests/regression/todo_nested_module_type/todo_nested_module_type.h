#ifndef INCLUDED_TODO_NESTED_MODULE_TYPE
#define INCLUDED_TODO_NESTED_MODULE_TYPE

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
    using t = unsigned int;
    static inline const unsigned int zero = 0u;
  };

  struct NatOuter {
    using Inner = NatInner;
    __attribute__((pure)) static Inner::t step(const unsigned int n);
  };

  using UseNat = Make<NatOuter>;
  static inline const unsigned int test_twice = UseNat::twice();
};

#endif // INCLUDED_TODO_NESTED_MODULE_TYPE
