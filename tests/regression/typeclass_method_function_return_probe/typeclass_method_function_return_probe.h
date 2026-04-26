#ifndef INCLUDED_TYPECLASS_METHOD_FUNCTION_RETURN_PROBE
#define INCLUDED_TYPECLASS_METHOD_FUNCTION_RETURN_PROBE

#include <concepts>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

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

enum class Bool0 { e_TRUE0, e_FALSE0 };
template <typename I, typename t_A>
concept Factory = requires(t_A a0, t_A a1) {
  { I::make(a0, a1) } -> std::convertible_to<t_A>;
};

struct TypeclassMethodFunctionReturnProbe {
  struct boolFactory {
    constexpr static Bool0 make(Bool0 x, Bool0 y) {
      switch (x) {
      case Bool0::e_TRUE0: {
        return y;
      }
      case Bool0::e_FALSE0: {
        return x;
      }
      default:
        std::unreachable();
      }
    }
  };

  static_assert(Factory<boolFactory, Bool0>);
  __attribute__((pure)) static Bool0 partial(const Bool0 _x0);
  static inline const Bool0 sample = partial(Bool0::e_FALSE0);
};

#endif // INCLUDED_TYPECLASS_METHOD_FUNCTION_RETURN_PROBE
