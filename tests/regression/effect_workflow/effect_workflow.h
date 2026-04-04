#ifndef INCLUDED_EFFECT_WORKFLOW
#define INCLUDED_EFFECT_WORKFLOW

#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <filesystem>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <unistd.h>
#include <utility>
#include <variant>

using namespace std::string_literals;
template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct EffectWorkflow {
  /// 1. Use 5 different effect types in one function
  static std::string full_workflow(const std::string prefix);
  /// 2. Match on bool from create_directory inside a chain
  static std::string conditional_create(const std::string path);
  /// 3. get_line (block template) followed by env set using the result
  static void read_and_set();
  /// 4. Recursive function using effects
  static unsigned int repeat_log(const unsigned int n, const std::string msg);
  /// 5. Effect returning option, matched, then another effect
  static std::string env_or_create(const std::string name,
                                   const std::string path);
  /// 6. Pure let after block template
  static int64_t read_length();
  /// 7. Multiple block templates of different types
  static std::pair<std::string, std::string> double_read();
  /// 8. Return int literal in monadic context
  static int64_t return_literal();
};

#endif // INCLUDED_EFFECT_WORKFLOW
