#ifndef INCLUDED_EFFECT_BARE_VOID
#define INCLUDED_EFFECT_BARE_VOID

#include <cstdlib>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct EffectBareVoid {
  /// 1. Bare print_endline as function body (no bind, no Ret)
  static void just_print(const std::string msg);
  /// 2. Bare set_env as function body
  static void just_set(const std::string k, const std::string v);
  /// 3. Print then Ret tt (normal pattern for comparison)
  static void print_then_ret(const std::string msg);
  /// 4. Void effect in conditional — both branches are bare effects
  static void cond_print(const bool &flag, const std::string msg);
  /// 5. Set env then print (chained void effects)
  static void set_then_print(const std::string k, const std::string v);
  /// 6. Bare get_line (value-returning effect as sole body)
  static std::string just_read();
  /// 7. Bare get_env (value-returning, returns option)
  static std::optional<std::string> just_get_env(const std::string name);
};

#endif // INCLUDED_EFFECT_BARE_VOID
