#ifndef INCLUDED_TODO_WITH_MODULE_CONSTRAINT
#define INCLUDED_TODO_WITH_MODULE_CONSTRAINT

#include <concepts>
#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_unique<T>(x->clone()) : nullptr;
  } else {
    return x ? std::make_unique<T>(*x) : nullptr;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using T = std::remove_cvref_t<Target>;
  using S = std::remove_cvref_t<Source>;
  if constexpr (requires(const S &s) {
                  s.has_value();
                  *s;
                }) {
    if (!x.has_value())
      return T{};
    using TInner = std::remove_cvref_t<decltype(*std::declval<const T &>())>;
    return T{clone_as_value<TInner>(*x)};
  } else if constexpr (std::is_same_v<T, S>) {
    if constexpr (is_unique_ptr<T>::value) {
      return clone_value(x);
    } else if constexpr (requires { x.clone(); }) {
      return x.clone();
    } else {
      return x;
    }
  } else if constexpr (is_unique_ptr<S>::value) {
    if (!x)
      return T{};
    return clone_as_value<T>(*x);
  } else if constexpr (is_unique_ptr<T>::value) {
    using Inner = typename is_unique_ptr<T>::element_type;
    return std::make_unique<Inner>(clone_as_value<Inner>(x));
  } else {
    return T(x);
  }
}

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
    __attribute__((pure)) static Inner::t step(unsigned int n);
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
