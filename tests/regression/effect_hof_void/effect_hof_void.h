#ifndef INCLUDED_EFFECT_HOF_VOID
#define INCLUDED_EFFECT_HOF_VOID

#include <cstdlib>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <variant>

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

struct EffectHofVoid {
  /// 1. Apply a void callback
  template <MapsTo<void, std::string> F0>
  static void apply_void(F0 &&f, const std::string _x0) {
    f(_x0);
    return;
  }

  /// 2. Apply a void callback then return a value
  template <MapsTo<void, std::string> F0>
  static std::string apply_then_return(F0 &&f, const std::string x) {
    f(x);
    return x;
  } /// 3. Apply a value callback

  template <typename F0>
  static std::string apply_value(F0 &&f, const std::string x) {
    return f(x);
  }

  /// 4. Apply callback conditionally
  template <MapsTo<void, std::string> F1>
  static void apply_if(const bool &flag, F1 &&f, const std::string x) {
    if (flag) {
      f(x);
      return;
    } else {
      return;
    }
  }

  /// 5. Chain two void callbacks
  template <MapsTo<void, std::string> F0, MapsTo<void, std::string> F1>
  static void chain_void(F0 &&f, F1 &&g, const std::string x) {
    f(x);
    g(x);
    return;
  } /// 6. Apply a callback N times

  template <MapsTo<void, std::string> F0>
  static unsigned int apply_n(F0 &&f, const std::string x,
                              const unsigned int &n) {
    if (n <= 0) {
      return 0u;
    } else {
      unsigned int n_ = n - 1;
      f(x);
      unsigned int rest = apply_n(f, x, n_);
      return (rest + 1);
    }
  }

  /// 7. Use print_endline as a concrete callback
  static std::string concrete_use();
  /// 8. Use set_env as a concrete callback via wrapper
  static void set_wrapper(const std::string v, const std::string k);
  static void concrete_set();
};

#endif // INCLUDED_EFFECT_HOF_VOID
