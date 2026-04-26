#ifndef INCLUDED_EFFECT_BARE_VOID
#define INCLUDED_EFFECT_BARE_VOID

#include <cstdlib>
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

struct EffectBareVoid {
  /// 1. Bare print_endline as function body (no bind, no Ret)
  static void just_print(const std::string msg);
  /// 2. Bare set_env as function body
  static void just_set(const std::string k, const std::string v);
  /// 3. Print then Ret tt (normal pattern for comparison)
  static void print_then_ret(const std::string msg);
  /// 4. Void effect in conditional — both branches are bare effects
  static void cond_print(const bool &flag, const std::string msg);
  /// 5. Set env then print (chained void effects)
  static void set_then_print(const std::string k, const std::string v);
  /// 6. Bare get_line (value-returning effect as sole body)
  static std::string just_read();
  /// 7. Bare get_env (value-returning, returns option)
  static std::optional<std::string> just_get_env(const std::string name);
};

#endif // INCLUDED_EFFECT_BARE_VOID
