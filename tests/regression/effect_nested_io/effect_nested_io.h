#ifndef INCLUDED_EFFECT_NESTED_IO
#define INCLUDED_EFFECT_NESTED_IO

#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

using namespace std::string_literals;
template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct EffectNestedIo {
  /// 1. Block template result used inside constructor (Some)
  static std::optional<std::string> read_optional();
  /// 2. Block template result used in a pair
  static std::pair<std::string, int64_t> read_pair();
  /// 3. Block template result concatenated with another string
  static std::string read_and_greet();
  /// 4. Two block templates, results used in pair
  static std::pair<std::string, std::string> read_two_lines();
  /// 5. Block template in function that also uses clock effect
  static std::pair<std::string, int64_t> timed_read();
  /// 6. Block template result stored in env
  static std::string read_and_store(const std::string key);
  /// 7. Multiple block templates interleaved with env effects
  static std::pair<std::string, std::string> multi_read_store();
  /// 8. Block template result length checked
  static int64_t read_length();
};

#endif // INCLUDED_EFFECT_NESTED_IO
