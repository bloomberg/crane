#ifndef INCLUDED_EFFECT_OPTION_STRING
#define INCLUDED_EFFECT_OPTION_STRING

#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>

using namespace std::string_literals;

struct EffectOptionString {
  static std::string let_option_match(std::string name);
  static std::string bind_option_match(std::string name);
  static std::string option_effect_or_literal(std::string name);
  static std::string nested_option(std::string n1, std::string n2);
  static void option_then_effect(std::string name);
  static int64_t option_int(std::string name);
};

#endif // INCLUDED_EFFECT_OPTION_STRING
