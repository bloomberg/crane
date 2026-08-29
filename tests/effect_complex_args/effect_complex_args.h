#ifndef INCLUDED_EFFECT_COMPLEX_ARGS
#define INCLUDED_EFFECT_COMPLEX_ARGS

#include <cstdlib>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>

using namespace std::string_literals;

struct EffectComplexArgs {
  static void set_prefixed(std::string prefix, std::string suffix,
                           std::string value);
  static void set_with_value(std::string key, std::string prefix,
                             std::string suffix);
  static std::optional<std::string> get_prefixed(std::string prefix,
                                                 std::string suffix);
  static void print_concat(std::string a, std::string b);
  static std::optional<std::string>
  round_trip(std::string prefix, std::string suffix, std::string value);
  static void deep_concat(std::string a, std::string b, std::string c);
  static void chain_with_concat(std::string name);
  static void unset_prefixed(std::string prefix, std::string suffix);
};

#endif // INCLUDED_EFFECT_COMPLEX_ARGS
