#pragma once

#include <crane_string.h>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <variant>

struct EffectOptionString {
  /// 1. Pure let binding with option match — Some returns variable,
  /// None returns string literal
  static std::string let_option_match(const std::string &name);
  /// 2. Option match as bind action — Some returns Ret of variable,
  /// None returns Ret of string literal
  static std::string bind_option_match(const std::string &name);
  /// 3. Option match where Some arm has an effect and None arm returns literal
  static std::string option_effect_or_literal(const std::string &name);
  /// 4. Nested option matches: match on option, inside Some branch
  /// do another get_env and match
  static std::string nested_option(const std::string &n1,
                                   const std::string &n2);
  /// 5. Option match result fed directly to an effect
  static void option_then_effect(const std::string &name);
  /// 6. Option match with int result
  static int64_t option_int(const std::string &name);
};
