#ifndef INCLUDED_EFFECT_BIND_ACTION
#define INCLUDED_EFFECT_BIND_ACTION

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

struct EffectBindAction {
  /// 1. Bool match inside bind action: one branch block template
  static std::string conditional_read(const bool &use_stdin);
  /// 2. Bool match where both branches are effects
  static int64_t conditional_effect(const bool &flag);
  /// 3. Option match inside bind: conditional effect based on env
  static std::string maybe_override(const std::string name,
                                    const std::string default0);
  /// 4. Nested: effect result used in another conditional effect
  static std::pair<int64_t, int64_t> timed_if_needed(bool measure);
  /// 5. Block template get_line, then conditional print
  static std::string echo_if(bool flag);
  /// 6. Effect action that's a function application (not inlined)
  static std::string helper(const std::string s);
  static std::string use_helper(const bool &flag);
  /// 7. Let-binding of a match result, then use in effect
  static std::string let_match_then_effect(const unsigned int &n);
  /// 8. Discard result of conditional effect
  static unsigned int discard_conditional(const bool &flag);
};

#endif // INCLUDED_EFFECT_BIND_ACTION
