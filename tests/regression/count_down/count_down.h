#ifndef INCLUDED_COUNT_DOWN
#define INCLUDED_COUNT_DOWN

#include <filesystem>
#include <fstream>
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

enum class Comparison { e_EQ, e_LT, e_GT };

struct CountDown {
  /// Single effect then recurse: effect ;; recursive_call
  static void count_down(const unsigned int &n);
  /// Two effects then recurse: effect ;; effect ;; recursive_call
  static void two_prints(const unsigned int &n);
  /// Read from user, echo back, then recurse
  static void echo_loop(const unsigned int &n);
  /// Effect in base case too: both branches do IO
  static void announce(const unsigned int &n);
  /// Multiple arguments: two nat params, recurse on first
  static void repeat_msg(const unsigned int &n, const std::string msg);
  static void run_fixpoint();
  /// Helper: compare two strings
  __attribute__((pure)) static bool string_eq(const std::string s1,
                                              const std::string s2);
  static void co_count_down();
  static void co_two_prints();
  static void co_echo_loop();
  static void co_announce(unsigned int round);
  static void co_repeat(const std::string msg);
};

#endif // INCLUDED_COUNT_DOWN
