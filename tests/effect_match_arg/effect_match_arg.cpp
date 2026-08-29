#include "effect_match_arg.h"

void EffectMatchArg::set_bool_value(bool flag, std::string key) {
  setenv(
      key.c_str(),
      [&]() -> std::string {
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

void EffectMatchArg::set_bool_key(bool flag, std::string value) {
  setenv(
      [&]() -> std::string {
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

void EffectMatchArg::set_option_value(std::string key,
                                      const std::optional<std::string> &r) {
  setenv(
      key.c_str(),
      [&]() -> std::string {
        if (r.has_value()) {
          const std::string &v = *r;
          return v;
        } else {
          return "default";
        }
      }()
                   .c_str(),
      1);
  return;
}

void EffectMatchArg::print_conditional(bool flag) {
  std::cout << [&]() -> std::string {
    if (flag) {
      return "TRUE";
    } else {
      return "FALSE";
    }
  }() << '\n';
  return;
}

std::optional<std::string> EffectMatchArg::get_conditional(bool flag) {
  return [&]() -> std::optional<std::string> {
    auto *v = std::getenv([=]() mutable -> std::string {
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

std::optional<std::string> EffectMatchArg::round_trip_match(bool flag) {
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
