#pragma once

#include <crane_string.h>
#include <cstdlib>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <variant>

struct EffectComplexArgs {
  /// 1. set_env with concatenated key — complex expr as first arg
  static void set_prefixed(const std::string &prefix, const std::string &suffix,
                           const std::string &value);
  /// 2. set_env with concatenated value — complex expr as second arg
  static void set_with_value(const std::string &key, const std::string &prefix,
                             const std::string &suffix);
  /// 3. get_env with concatenated name
  static std::optional<std::string> get_prefixed(const std::string &prefix,
                                                 const std::string &suffix);
  /// 4. print_endline with concatenated string
  static void print_concat(const std::string &a, const std::string &b);
  /// 5. Chained: build key, set env, then get env
  static std::optional<std::string> round_trip(const std::string &prefix,
                                               const std::string &suffix,
                                               const std::string &value);
  /// 6. Nested concatenation as argument
  static void deep_concat(const std::string &a, const std::string &b,
                          const std::string &c);
  /// 7. Effect result used in concatenation for another effect
  static void chain_with_concat(const std::string &name);
  /// 8. unset_env with concatenated key
  static void unset_prefixed(const std::string &prefix,
                             const std::string &suffix);
};
