#ifndef INCLUDED_EFFECT_NESTED_IO
#define INCLUDED_EFFECT_NESTED_IO

#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>

using namespace std::string_literals;

struct EffectNestedIo {
  static std::optional<std::string> read_optional();
  static std::pair<std::string, int64_t> read_pair();
  static std::string read_and_greet();
  static std::pair<std::string, std::string> read_two_lines();
  static std::pair<std::string, int64_t> timed_read();
  static std::string read_and_store(std::string key);
  static std::pair<std::string, std::string> multi_read_store();
  static int64_t read_length();
};

#endif // INCLUDED_EFFECT_NESTED_IO
