#ifndef INCLUDED_EFFECT_DEEP_COMPOSE
#define INCLUDED_EFFECT_DEEP_COMPOSE

#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <variant>

using namespace std::string_literals;

struct EffectDeepCompose {
  static int64_t timed_env_op(std::string name, std::string value);
  static void just_greet();
  static void env_with_log(std::string name, std::string value);
  static void show_env(std::string name);
  static int64_t maybe_time(bool measure);
  static void repeat_n(uint64_t n);
};

#endif // INCLUDED_EFFECT_DEEP_COMPOSE
