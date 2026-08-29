#ifndef INCLUDED_EFFECT_BIND_ACTION
#define INCLUDED_EFFECT_BIND_ACTION

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

struct EffectBindAction {
  static std::string conditional_read(bool use_stdin);
  static int64_t conditional_effect(bool flag);
  static std::string maybe_override(std::string name, std::string default0);
  static std::pair<int64_t, int64_t> timed_if_needed(bool measure);
  static std::string echo_if(bool flag);
  static std::string helper(std::string s);
  static std::string use_helper(bool flag);
  static std::string let_match_then_effect(uint64_t n);
  static uint64_t discard_conditional(bool flag);
};

#endif // INCLUDED_EFFECT_BIND_ACTION
