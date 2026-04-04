#include <effect_complex_args.h>

#include <cstdlib>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <variant>

/// 1. set_env with concatenated key — complex expr as first arg
void EffectComplexArgs::set_prefixed(const std::string prefix,
                                     const std::string suffix,
                                     const std::string value) {
  setenv(prefix + suffix.c_str(), value.c_str(), 1);
  return;
}

/// 2. set_env with concatenated value — complex expr as second arg
void EffectComplexArgs::set_with_value(const std::string key,
                                       const std::string prefix,
                                       const std::string suffix) {
  setenv(key.c_str(), prefix + suffix.c_str(), 1);
  return;
}

/// 3. get_env with concatenated name
std::optional<std::string>
EffectComplexArgs::get_prefixed(const std::string prefix,
                                const std::string suffix) {
  return [&]() -> std::optional<std::string> {
    auto *v = std::getenv(prefix + suffix.c_str());
    return v ? std::optional<std::string>(v) : std::optional<std::string>();
  }();
}

/// 4. print_endline with concatenated string
void EffectComplexArgs::print_concat(const std::string a, const std::string b) {
  std::cout << a + b << '\n';
  return;
}

/// 5. Chained: build key, set env, then get env
std::optional<std::string>
EffectComplexArgs::round_trip(const std::string prefix,
                              const std::string suffix,
                              const std::string value) {
  std::string key = prefix + suffix;
  setenv(key.c_str(), value.c_str(), 1);
  return [&]() -> std::optional<std::string> {
    auto *v = std::getenv(key.c_str());
    return v ? std::optional<std::string>(v) : std::optional<std::string>();
  }();
}

/// 6. Nested concatenation as argument
void EffectComplexArgs::deep_concat(const std::string a, const std::string b,
                                    const std::string c) {
  setenv(a + b + c.c_str(), "value"s.c_str(), 1);
  return;
}

/// 7. Effect result used in concatenation for another effect
void EffectComplexArgs::chain_with_concat(const std::string name) {
  std::optional<std::string> r = [&]() -> std::optional<std::string> {
    auto *v = std::getenv(name.c_str());
    return v ? std::optional<std::string>(v) : std::optional<std::string>();
  }();
  if (r.has_value()) {
    std::string v = *r;
    setenv("COPY_"s + name.c_str(), v.c_str(), 1);
    return;
  } else {
    return;
  }
}

/// 8. unset_env with concatenated key
void EffectComplexArgs::unset_prefixed(const std::string prefix,
                                       const std::string suffix) {
  unsetenv(prefix + suffix.c_str());
  return;
}
