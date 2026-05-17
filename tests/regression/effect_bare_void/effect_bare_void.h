#ifndef INCLUDED_EFFECT_BARE_VOID
#define INCLUDED_EFFECT_BARE_VOID

#include <cstdlib>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <variant>

struct EffectBareVoid {
  /// 1. Bare print_endline as function body (no bind, no Ret)
  static void just_print(std::string msg);
  /// 2. Bare set_env as function body
  static void just_set(std::string k, std::string v);
  /// 3. Print then Ret tt (normal pattern for comparison)
  static void print_then_ret(std::string msg);
  /// 4. Void effect in conditional — both branches are bare effects
  static void cond_print(bool flag, std::string msg);
  /// 5. Set env then print (chained void effects)
  static void set_then_print(std::string k, std::string v);
  /// 6. Bare get_line (value-returning effect as sole body)
  static std::string just_read();
  /// 7. Bare get_env (value-returning, returns option)
  static std::optional<std::string> just_get_env(std::string name);
};

#endif // INCLUDED_EFFECT_BARE_VOID
