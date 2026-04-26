#ifndef INCLUDED_EFFECT_COMPLEX_ARGS
#define INCLUDED_EFFECT_COMPLEX_ARGS

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

struct EffectComplexArgs {
  /// 1. set_env with concatenated key — complex expr as first arg
  static void set_prefixed(const std::string prefix, const std::string suffix,
                           const std::string value);
  /// 2. set_env with concatenated value — complex expr as second arg
  static void set_with_value(const std::string key, const std::string prefix,
                             const std::string suffix);
  /// 3. get_env with concatenated name
  static std::optional<std::string> get_prefixed(const std::string prefix,
                                                 const std::string suffix);
  /// 4. print_endline with concatenated string
  static void print_concat(const std::string a, const std::string b);
  /// 5. Chained: build key, set env, then get env
  static std::optional<std::string> round_trip(const std::string prefix,
                                               const std::string suffix,
                                               const std::string value);
  /// 6. Nested concatenation as argument
  static void deep_concat(const std::string a, const std::string b,
                          const std::string c);
  /// 7. Effect result used in concatenation for another effect
  static void chain_with_concat(const std::string name);
  /// 8. unset_env with concatenated key
  static void unset_prefixed(const std::string prefix,
                             const std::string suffix);
};

#endif // INCLUDED_EFFECT_COMPLEX_ARGS
