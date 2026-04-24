#include <effect_option_string.h>

#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <variant>

/// 1. Pure let binding with option match — Some returns variable,
/// None returns string literal
std::string EffectOptionString::let_option_match(const std::string name) {
  std::optional<std::string> r = [&]() -> std::optional<std::string> {
    auto *v = std::getenv(name.c_str());
    return v ? std::optional<std::string>(v) : std::optional<std::string>();
  }();
  std::string s;
  if (r.has_value()) {
    const std::string &v = *r;
    s = v;
  } else {
    s = "unknown";
  }
  return s;
}

/// 2. Option match as bind action — Some returns Ret of variable,
/// None returns Ret of string literal
std::string EffectOptionString::bind_option_match(const std::string name) {
  std::optional<std::string> r = [&]() -> std::optional<std::string> {
    auto *v = std::getenv(name.c_str());
    return v ? std::optional<std::string>(v) : std::optional<std::string>();
  }();
  return [=]() mutable -> std::string {
    if (r.has_value()) {
      const std::string &v = *r;
      return v;
    } else {
      return "fallback";
    }
  }();
}

/// 3. Option match where Some arm has an effect and None arm returns literal
std::string
EffectOptionString::option_effect_or_literal(const std::string name) {
  std::optional<std::string> r = [&]() -> std::optional<std::string> {
    auto *v = std::getenv(name.c_str());
    return v ? std::optional<std::string>(v) : std::optional<std::string>();
  }();
  if (r.has_value()) {
    const std::string &_x = *r;
    return []() -> std::string {
      std::string _r;
      std::getline(std::cin, _r);
      return _r;
    }();
  } else {
    return "no_input";
  }
}

/// 4. Nested option matches: match on option, inside Some branch
/// do another get_env and match
std::string EffectOptionString::nested_option(const std::string n1,
                                              const std::string n2) {
  std::optional<std::string> r1 = [&]() -> std::optional<std::string> {
    auto *v = std::getenv(n1.c_str());
    return v ? std::optional<std::string>(v) : std::optional<std::string>();
  }();
  if (r1.has_value()) {
    const std::string &v1 = *r1;
    std::optional<std::string> r2 = [&]() -> std::optional<std::string> {
      auto *v = std::getenv(n2.c_str());
      return v ? std::optional<std::string>(v) : std::optional<std::string>();
    }();
    if (r2.has_value()) {
      const std::string &v2 = *r2;
      return v1 + "/"s + v2;
    } else {
      return v1;
    }
  } else {
    return "none";
  }
}

/// 5. Option match result fed directly to an effect
void EffectOptionString::option_then_effect(const std::string name) {
  std::optional<std::string> r = [&]() -> std::optional<std::string> {
    auto *v = std::getenv(name.c_str());
    return v ? std::optional<std::string>(v) : std::optional<std::string>();
  }();
  std::string msg;
  if (r.has_value()) {
    const std::string &v = *r;
    msg = v;
  } else {
    msg = "not_set";
  }
  std::cout << msg << '\n';
  return;
}

/// 6. Option match with int result
int64_t EffectOptionString::option_int(const std::string name) {
  std::optional<std::string> r = [&]() -> std::optional<std::string> {
    auto *v = std::getenv(name.c_str());
    return v ? std::optional<std::string>(v) : std::optional<std::string>();
  }();
  int64_t len;
  if (r.has_value()) {
    const std::string &v = *r;
    len = v.length();
  } else {
    len = int64_t(0);
  }
  return len;
}
