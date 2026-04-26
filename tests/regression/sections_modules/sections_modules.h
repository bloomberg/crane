#ifndef INCLUDED_SECTIONS_MODULES
#define INCLUDED_SECTIONS_MODULES

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
concept Semigroup = requires {
  typename M::T;
  {
    M::op(std::declval<typename M::T>(), std::declval<typename M::T>())
  } -> std::same_as<typename M::T>;
};
template <typename M>
concept HasIdentity = requires {
  typename M::T;
  requires(
      requires {
        { M::id } -> std::convertible_to<typename M::T>;
      } ||
      requires {
        { M::id() } -> std::convertible_to<typename M::T>;
      });
};
template <typename M>
concept Monoid = requires {
  typename M::T;
  {
    M::op(std::declval<typename M::T>(), std::declval<typename M::T>())
  } -> std::same_as<typename M::T>;
  requires(
      requires {
        { M::id } -> std::convertible_to<typename M::T>;
      } ||
      requires {
        { M::id() } -> std::convertible_to<typename M::T>;
      });
};

struct SectionsModules {
  __attribute__((pure)) static unsigned int add_params(const unsigned int &x,
                                                       const unsigned int &y,
                                                       const unsigned int &n);
  __attribute__((pure)) static unsigned int
  count_down_from_x(unsigned int x, const unsigned int &y,
                    const unsigned int &n);

  struct NatMonoid {
    using T = unsigned int;
    __attribute__((pure)) static unsigned int op(const unsigned int &_x0,
                                                 const unsigned int &_x1);
    static inline const unsigned int id = 0u;
  };

  using TransparentMod = NatMonoid;
  static inline const unsigned int use_monoid = TransparentMod::op(5u, 10u);

  template <Semigroup M> struct MakeDoubleOp {
    constexpr static typename M::T double_(const typename M::T x) {
      return M::op(x, x);
    }

    constexpr static typename M::T quad(const typename M::T x) {
      return double_(double_(x));
    }
  };

  using NatDoubleOp = MakeDoubleOp<NatMonoid>;
  static inline const NatMonoid::T test_double = NatDoubleOp::double_(5u);

  struct LocalDefs {
    __attribute__((pure)) static unsigned int
    private_helper(const unsigned int &n);
    __attribute__((pure)) static unsigned int public_use(const unsigned int &n);
  };

  __attribute__((pure)) static unsigned int
  use_both(const unsigned int &a, const unsigned int &b, const unsigned int &c);
  __attribute__((pure)) static unsigned int use_outer(const unsigned int &_x0,
                                                      const unsigned int &_x1);

  struct Base {
    static inline const unsigned int base_val = 42u;
    __attribute__((pure)) static unsigned int base_fun(const unsigned int &n);
  };

  struct Extended {
    static inline const unsigned int base_val = 42u;
    __attribute__((pure)) static unsigned int base_fun(const unsigned int &n);
    static inline const unsigned int extended_val = 100u;
    __attribute__((pure)) static unsigned int
    extended_fun(const unsigned int &n);
  };

  static inline const unsigned int test_extended =
      Extended::extended_fun(Extended::base_val);
};

#endif // INCLUDED_SECTIONS_MODULES
