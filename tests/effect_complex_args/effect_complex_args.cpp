#include "effect_complex_args.h"

void EffectComplexArgs::set_prefixed(std::string prefix, std::string suffix,
                                     std::string value) {
  setenv((prefix + suffix).c_str(), value.c_str(), 1);
  return;
}

void EffectComplexArgs::set_with_value(std::string key, std::string prefix,
                                       std::string suffix) {
  setenv(key.c_str(), (prefix + suffix).c_str(), 1);
  return;
}

std::optional<std::string> EffectComplexArgs::get_prefixed(std::string prefix,
                                                           std::string suffix) {
  return [&]() -> std::optional<std::string> {
    auto *v = std::getenv((prefix + suffix).c_str());
    return v ? std::optional<std::string>(v) : std::optional<std::string>();
  }();
}

void EffectComplexArgs::print_concat(std::string a, std::string b) {
  std::cout << a + b << '\n';
  return;
}

std::optional<std::string> EffectComplexArgs::round_trip(std::string prefix,
                                                         std::string suffix,
                                                         std::string value) {
  std::string key = prefix + suffix;
  setenv(key.c_str(), value.c_str(), 1);
  return [&]() -> std::optional<std::string> {
    auto *v = std::getenv(std::move(key).c_str());
    return v ? std::optional<std::string>(v) : std::optional<std::string>();
  }();
}

void EffectComplexArgs::deep_concat(std::string a, std::string b,
                                    std::string c) {
  setenv((a + b + c).c_str(), "value"s.c_str(), 1);
  return;
}

void EffectComplexArgs::chain_with_concat(std::string name) {
  std::optional<std::string> r = [&]() -> std::optional<std::string> {
    auto *v = std::getenv(name.c_str());
    return v ? std::optional<std::string>(v) : std::optional<std::string>();
  }();
  if (r.has_value()) {
    const std::string &v = *r;
    setenv(("COPY_"s + name).c_str(), v.c_str(), 1);
    return;
  } else {
    return;
  }
}

void EffectComplexArgs::unset_prefixed(std::string prefix, std::string suffix) {
  unsetenv((prefix + suffix).c_str());
  return;
}
