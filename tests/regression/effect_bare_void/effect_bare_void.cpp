#include <effect_bare_void.h>

#include <cstdlib>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <variant>

/// 1. Bare print_endline as function body (no bind, no Ret)
void EffectBareVoid::just_print(const std::string msg) {
  std::cout << msg << '\n';
  return;
}

/// 2. Bare set_env as function body
void EffectBareVoid::just_set(const std::string k, const std::string v) {
  setenv(k.c_str(), v.c_str(), 1);
  return;
}

/// 3. Print then Ret tt (normal pattern for comparison)
void EffectBareVoid::print_then_ret(const std::string msg) {
  std::cout << msg << '\n';
  return;
}

/// 4. Void effect in conditional — both branches are bare effects
void EffectBareVoid::cond_print(const bool flag, const std::string msg) {
  if (flag) {
    std::cout << msg << '\n';
    return;
  } else {
    return;
  }
}

/// 5. Set env then print (chained void effects)
void EffectBareVoid::set_then_print(const std::string k, const std::string v) {
  setenv(k.c_str(), v.c_str(), 1);
  std::cout << v << '\n';
  return;
}

/// 6. Bare get_line (value-returning effect as sole body)
std::string EffectBareVoid::just_read() {
  return [&]() -> std::string {
    std::string _r;
    std::getline(std::cin, _r);
    return _r;
  }();
}

/// 7. Bare get_env (value-returning, returns option)
std::optional<std::string>
EffectBareVoid::just_get_env(const std::string name) {
  return [&]() -> std::optional<std::string> {
    auto *v = std::getenv(name.c_str());
    return v ? std::optional<std::string>(v) : std::optional<std::string>();
  }();
}
