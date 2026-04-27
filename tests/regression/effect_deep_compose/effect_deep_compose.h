#ifndef INCLUDED_EFFECT_DEEP_COMPOSE
#define INCLUDED_EFFECT_DEEP_COMPOSE

#include <chrono>
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

struct EffectDeepCompose {
  /// 1. Function using all three effects
  static int64_t timed_env_op(const std::string name, const std::string value);
  /// 2. Function using only console from inside bigE
  static void just_greet();
  /// 3. Function using env + console but not clock
  static void env_with_log(const std::string name, const std::string value);
  /// 4. Read env, print result
  static void show_env(const std::string name);
  /// 5. Conditional clock read
  static int64_t maybe_time(const bool &measure);
  /// 6. Recursive function over all three effects
  static void repeat_n(const unsigned int &n);
};

#endif // INCLUDED_EFFECT_DEEP_COMPOSE
