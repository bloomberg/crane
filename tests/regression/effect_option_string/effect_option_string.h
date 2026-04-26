#ifndef INCLUDED_EFFECT_OPTION_STRING
#define INCLUDED_EFFECT_OPTION_STRING

#include <cstdint>
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

struct EffectOptionString {
  /// 1. Pure let binding with option match — Some returns variable,
  /// None returns string literal
  static std::string let_option_match(const std::string name);
  /// 2. Option match as bind action — Some returns Ret of variable,
  /// None returns Ret of string literal
  static std::string bind_option_match(const std::string name);
  /// 3. Option match where Some arm has an effect and None arm returns literal
  static std::string option_effect_or_literal(const std::string name);
  /// 4. Nested option matches: match on option, inside Some branch
  /// do another get_env and match
  static std::string nested_option(const std::string n1, const std::string n2);
  /// 5. Option match result fed directly to an effect
  static void option_then_effect(const std::string name);
  /// 6. Option match with int result
  static int64_t option_int(const std::string name);
};

#endif // INCLUDED_EFFECT_OPTION_STRING
