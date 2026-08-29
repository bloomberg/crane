#include "effect_bare_void.h"

void EffectBareVoid::just_print(std::string msg) {
  std::cout << msg << '\n';
  return;
}

void EffectBareVoid::just_set(std::string k, std::string v) {
  setenv(k.c_str(), v.c_str(), 1);
  return;
}

void EffectBareVoid::print_then_ret(std::string msg) {
  std::cout << msg << '\n';
  return;
}

void EffectBareVoid::cond_print(bool flag, std::string msg) {
  if (flag) {
    std::cout << msg << '\n';
    return;
  } else {
    return;
  }
}

void EffectBareVoid::set_then_print(std::string k, std::string v) {
  setenv(k.c_str(), v.c_str(), 1);
  std::cout << v << '\n';
  return;
}

std::string EffectBareVoid::just_read() {
  return []() -> std::string {
    std::string _r;
    std::getline(std::cin, _r);
    return _r;
  }();
}

std::optional<std::string> EffectBareVoid::just_get_env(std::string name) {
  return [&]() -> std::optional<std::string> {
    auto *v = std::getenv(name.c_str());
    return v ? std::optional<std::string>(v) : std::optional<std::string>();
  }();
}
