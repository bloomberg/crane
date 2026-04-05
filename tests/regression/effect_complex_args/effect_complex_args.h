#ifndef INCLUDED_EFFECT_COMPLEX_ARGS
#define INCLUDED_EFFECT_COMPLEX_ARGS

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

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct EffectComplexArgs {
  /// 1. set_env with concatenated key — complex expr as first arg
  static void set_prefixed(const std::string prefix, const std::string suffix,
                           const std::string value);
  /// 2. set_env with concatenated value — complex expr as second arg
  static void set_with_value(const std::string key, const std::string prefix,
                             const std::string suffix);
  /// 3. get_env with concatenated name
  static std::optional<std::string> get_prefixed(const std::string prefix,
                                                 const std::string suffix);
  /// 4. print_endline with concatenated string
  static void print_concat(const std::string a, const std::string b);
  /// 5. Chained: build key, set env, then get env
  static std::optional<std::string> round_trip(const std::string prefix,
                                               const std::string suffix,
                                               const std::string value);
  /// 6. Nested concatenation as argument
  static void deep_concat(const std::string a, const std::string b,
                          const std::string c);
  /// 7. Effect result used in concatenation for another effect
  static void chain_with_concat(const std::string name);
  /// 8. unset_env with concatenated key
  static void unset_prefixed(const std::string prefix,
                             const std::string suffix);
};

#endif // INCLUDED_EFFECT_COMPLEX_ARGS
