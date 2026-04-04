#include <effect_match_arg.h>

#include <cstdlib>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <variant>

/// 1. Bool match as value argument to set_env
void EffectMatchArg::set_bool_value(const bool flag, const std::string key) {
  setenv(
      key.c_str(),
      [&]() {
        if (flag) {
          return "yes";
        } else {
          return "no";
        }
      }()
          .c_str(),
      1);
  return;
}

/// 2. Bool match as key argument to set_env
void EffectMatchArg::set_bool_key(const bool flag, const std::string value) {
  setenv(
      [&]() {
        if (flag) {
          return "KEY_A";
        } else {
          return "KEY_B";
        }
      }()
          .c_str(),
      value.c_str(), 1);
  return;
}

/// 3. Option match result as argument to set_env
void EffectMatchArg::set_option_value(const std::string key,
                                      const std::optional<std::string> r) {
  setenv(
      key.c_str(),
      [&]() {
        if (r.has_value()) {
          std::string v = *r;
          return v;
        } else {
          return "default";
        }
      }()
          .c_str(),
      1);
  return;
}

/// 4. Bool match as argument to print_endline — exercises << precedence
void EffectMatchArg::print_conditional(const bool flag) {
  std::cout << [&]() {
    if (flag) {
      return "TRUE";
    } else {
      return "FALSE";
    }
  }() << '\n';
  return;
}

/// 5. Bool match as argument to get_env
std::optional<std::string> EffectMatchArg::get_conditional(const bool flag) {
  return [&]() -> std::optional<std::string> {
    auto *v = std::getenv([&]() {
      if (flag) {
        return "KEY_A";
      } else {
        return "KEY_B";
      }
    }()
                              .c_str());
    return v ? std::optional<std::string>(v) : std::optional<std::string>();
  }();
}

/// 6. Chained: match result passed to set_env then get_env
std::optional<std::string> EffectMatchArg::round_trip_match(const bool flag) {
  std::string key;
  if (flag) {
    key = "X";
  } else {
    key = "Y";
  }
  setenv(key.c_str(), "val"s.c_str(), 1);
  return [&]() -> std::optional<std::string> {
    auto *v = std::getenv(key.c_str());
    return v ? std::optional<std::string>(v) : std::optional<std::string>();
  }();
}
