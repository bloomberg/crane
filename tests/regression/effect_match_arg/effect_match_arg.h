#ifndef INCLUDED_EFFECT_MATCH_ARG
#define INCLUDED_EFFECT_MATCH_ARG

#include <cstdlib>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <variant>

using namespace std::string_literals;
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

struct EffectMatchArg {
  /// 1. Bool match as value argument to set_env
  static void set_bool_value(const bool &flag, const std::string key);
  /// 2. Bool match as key argument to set_env
  static void set_bool_key(const bool &flag, const std::string value);
  /// 3. Option match result as argument to set_env
  static void set_option_value(const std::string key,
                               const std::optional<std::string> &r);
  /// 4. Bool match as argument to print_endline — exercises << precedence
  static void print_conditional(const bool &flag);
  /// 5. Bool match as argument to get_env
  static std::optional<std::string> get_conditional(const bool &flag);
  /// 6. Chained: match result passed to set_env then get_env
  static std::optional<std::string> round_trip_match(const bool &flag);
};

#endif // INCLUDED_EFFECT_MATCH_ARG
