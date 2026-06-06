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
  /// 1. set_env with concatenated key — complex expr as first arg
  static void set_prefixed(std::string prefix, std::string suffix,
                           std::string value);
  /// 2. set_env with concatenated value — complex expr as second arg
  static void set_with_value(std::string key, std::string prefix,
                             std::string suffix);
  /// 3. get_env with concatenated name
  static std::optional<std::string> get_prefixed(std::string prefix,
                                                 std::string suffix);
  /// 4. print_endline with concatenated string
  static void print_concat(std::string a, std::string b);
  /// 5. Chained: build key, set env, then get env
  static std::optional<std::string>
  round_trip(std::string prefix, std::string suffix, std::string value);
  /// 6. Nested concatenation as argument
  static void deep_concat(std::string a, std::string b, std::string c);
  /// 7. Effect result used in concatenation for another effect
  static void chain_with_concat(std::string name);
  /// 8. unset_env with concatenated key
  static void unset_prefixed(std::string prefix, std::string suffix);
};

#endif // INCLUDED_EFFECT_COMPLEX_ARGS
