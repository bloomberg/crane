#ifndef INCLUDED_EFFECT_WORKFLOW
#define INCLUDED_EFFECT_WORKFLOW

#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <filesystem>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <unistd.h>
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

struct EffectWorkflow {
  /// 1. Use 5 different effect types in one function
  static std::string full_workflow(const std::string prefix);
  /// 2. Match on bool from create_directory inside a chain
  static std::string conditional_create(const std::string path);
  /// 3. get_line (block template) followed by env set using the result
  static void read_and_set();
  /// 4. Recursive function using effects
  static unsigned int repeat_log(const unsigned int &n, const std::string msg);
  /// 5. Effect returning option, matched, then another effect
  static std::string env_or_create(const std::string name,
                                   const std::string path);
  /// 6. Pure let after block template
  static int64_t read_length();
  /// 7. Multiple block templates of different types
  static std::pair<std::string, std::string> double_read();
  /// 8. Return int literal in monadic context
  static int64_t return_literal();
};

#endif // INCLUDED_EFFECT_WORKFLOW
