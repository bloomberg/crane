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
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct EffectMatchArg {
  /// 1. Bool match as value argument to set_env
  static void set_bool_value(const bool flag, const std::string key);
  /// 2. Bool match as key argument to set_env
  static void set_bool_key(const bool flag, const std::string value);
  /// 3. Option match result as argument to set_env
  static void set_option_value(const std::string key,
                               const std::optional<std::string> r);
  /// 4. Bool match as argument to print_endline — exercises << precedence
  static void print_conditional(const bool flag);
  /// 5. Bool match as argument to get_env
  static std::optional<std::string> get_conditional(const bool flag);
  /// 6. Chained: match result passed to set_env then get_env
  static std::optional<std::string> round_trip_match(const bool flag);
};

#endif // INCLUDED_EFFECT_MATCH_ARG
