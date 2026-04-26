#ifndef INCLUDED_EFFECT_NESTED_IO
#define INCLUDED_EFFECT_NESTED_IO

#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <utility>
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

struct EffectNestedIo {
  /// 1. Block template result used inside constructor (Some)
  static std::optional<std::string> read_optional();
  /// 2. Block template result used in a pair
  static std::pair<std::string, int64_t> read_pair();
  /// 3. Block template result concatenated with another string
  static std::string read_and_greet();
  /// 4. Two block templates, results used in pair
  static std::pair<std::string, std::string> read_two_lines();
  /// 5. Block template in function that also uses clock effect
  static std::pair<std::string, int64_t> timed_read();
  /// 6. Block template result stored in env
  static std::string read_and_store(const std::string key);
  /// 7. Multiple block templates interleaved with env effects
  static std::pair<std::string, std::string> multi_read_store();
  /// 8. Block template result length checked
  static int64_t read_length();
};

#endif // INCLUDED_EFFECT_NESTED_IO
