#ifndef INCLUDED_EFFECT_HOF_VOID
#define INCLUDED_EFFECT_HOF_VOID

#include <cstdlib>
#include <functional>
#include <iostream>
#include <optional>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

struct EffectHofVoid {
  template <typename F0>
    requires std::is_invocable_r_v<void, F0 &, std::string &>
  static void apply_void(F0 &&f, std::string _x0) {
    f(std::move(_x0));
    return;
  }

  template <typename F0>
    requires std::is_invocable_r_v<void, F0 &, std::string &>
  static std::string apply_then_return(F0 &&f, std::string x) {
    f(x);
    return x;
  }

  template <typename F0> static std::string apply_value(F0 &&f, std::string x) {
    return f(x);
  }

  template <typename F1>
    requires std::is_invocable_r_v<void, F1 &, std::string &>
  static void apply_if(bool flag, F1 &&f, std::string x) {
    if (flag) {
      f(x);
      return;
    } else {
      return;
    }
  }

  template <typename F0, typename F1>
    requires std::is_invocable_r_v<void, F0 &, std::string &> &&
             std::is_invocable_r_v<void, F1 &, std::string &>
  static void chain_void(F0 &&f, F1 &&g, std::string x) {
    f(x);
    g(x);
    return;
  }

  template <typename F0>
    requires std::is_invocable_r_v<void, F0 &, std::string &>
  static uint64_t apply_n(F0 &&f, std::string x, uint64_t n) {
    if (n <= 0) {
      return UINT64_C(0);
    } else {
      uint64_t n_ = n - 1;
      f(x);
      uint64_t rest = apply_n(f, x, n_);
      return (rest + 1);
    }
  }

  static std::string concrete_use();
  static void set_wrapper(std::string v, std::string k);
  static void concrete_set();
};

#endif // INCLUDED_EFFECT_HOF_VOID
