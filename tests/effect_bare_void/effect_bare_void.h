#ifndef INCLUDED_EFFECT_BARE_VOID
#define INCLUDED_EFFECT_BARE_VOID

#include <cstdlib>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <variant>

struct EffectBareVoid {
  static void just_print(std::string msg);
  static void just_set(std::string k, std::string v);
  static void print_then_ret(std::string msg);
  static void cond_print(bool flag, std::string msg);
  static void set_then_print(std::string k, std::string v);
  static std::string just_read();
  static std::optional<std::string> just_get_env(std::string name);
};

#endif // INCLUDED_EFFECT_BARE_VOID
