#include "effect_option_string.h"

std::string EffectOptionString::let_option_match(std::string name) {
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

std::string EffectOptionString::bind_option_match(std::string name) {
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

std::string EffectOptionString::option_effect_or_literal(std::string name) {
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

std::string EffectOptionString::nested_option(std::string n1, std::string n2) {
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

void EffectOptionString::option_then_effect(std::string name) {
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
  std::cout << std::move(msg) << '\n';
  return;
}

int64_t EffectOptionString::option_int(std::string name) {
  std::optional<std::string> r = [&]() -> std::optional<std::string> {
    auto *v = std::getenv(name.c_str());
    return v ? std::optional<std::string>(v) : std::optional<std::string>();
  }();
  int64_t len;
  if (r.has_value()) {
    const std::string &v = *r;
    len = static_cast<int64_t>(v.length());
  } else {
    len = INT64_C(0);
  }
  return len;
}
