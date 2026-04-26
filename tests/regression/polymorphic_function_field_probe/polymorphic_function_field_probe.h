#ifndef INCLUDED_POLYMORPHIC_FUNCTION_FIELD_PROBE
#define INCLUDED_POLYMORPHIC_FUNCTION_FIELD_PROBE

#include <any>
#include <functional>
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

enum class Bool0 { e_TRUE0, e_FALSE0 };

struct PolymorphicFunctionFieldProbe {
  struct poly {
    std::function<std::any(std::any)> apply;

    __attribute__((pure)) poly *operator->() { return this; }

    __attribute__((pure)) const poly *operator->() const { return this; }

    // ACCESSORS
    __attribute__((pure)) poly clone() const { return poly{(*(this)).apply}; }
  };

  template <typename T1> static T1 apply(const poly &p0, const T1 x) {
    return std::any_cast<T1>(p0.apply(x));
  }

  static inline const poly p = poly{[](const std::any x) { return x; }};
  static inline const Bool0 sample_bool = apply<Bool0>(p, Bool0::e_TRUE0);
};

#endif // INCLUDED_POLYMORPHIC_FUNCTION_FIELD_PROBE
