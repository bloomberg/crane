#ifndef INCLUDED_EFFECT_MATCH_ARG
#define INCLUDED_EFFECT_MATCH_ARG

#include <cstdlib>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <variant>

using namespace std::string_literals;

struct EffectMatchArg {
  static void set_bool_value(bool flag, std::string key);
  static void set_bool_key(bool flag, std::string value);
  static void set_option_value(std::string key,
                               const std::optional<std::string> &r);
  static void print_conditional(bool flag);
  static std::optional<std::string> get_conditional(bool flag);
  static std::optional<std::string> round_trip_match(bool flag);
};

#endif // INCLUDED_EFFECT_MATCH_ARG
