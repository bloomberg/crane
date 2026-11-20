#pragma once

#include "fn.h"
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <string>
#include <string_view>
#include <type_traits>
#include <variant>

struct EffectHofVoid {
  /// 1. Apply a void callback
  template <typename F0>
    requires std::is_invocable_r_v<void, F0 &, const std::string &>
  static void apply_void(F0 &&f, const std::string &x0_) {
    f(x0_);
    return;
  }

  /// 2. Apply a void callback then return a value
  template <typename F0>
    requires std::is_invocable_r_v<void, F0 &, const std::string &>
  static std::string apply_then_return(F0 &&f, const std::string &x) {
    f(x);
    return x;
  }

  /// 3. Apply a value callback
  template <typename F0>
  static std::string apply_value(F0 &&f, const std::string &x) {
    return f(x);
  }

  /// 4. Apply callback conditionally
  template <typename F1>
  static void apply_if(bool flag, F1 &&f, const std::string &x) {
    if (flag) {
      f(x);
      return;
    } else {
      return;
    }
  }

  /// 5. Chain two void callbacks
  template <typename F0, typename F1>
    requires std::is_invocable_r_v<void, F0 &, const std::string &> &&
             std::is_invocable_r_v<void, F1 &, const std::string &>
  static void chain_void(F0 &&f, F1 &&g, const std::string &x) {
    f(x);
    g(x);
    return;
  }

  /// 6. Apply a callback N times
  template <typename F0>
  static uint64_t apply_n(F0 &&f, const std::string &x, uint64_t n) {
    if (n <= 0) {
      return UINT64_C(0);
    } else {
      uint64_t n_ = n - 1;
      f(x);
      uint64_t rest = apply_n(f, x, n_);
      return (rest + 1);
    }
  }

  /// 7. Use print_endline as a concrete callback
  static std::string concrete_use();
  /// 8. Use set_env as a concrete callback via wrapper
  static void set_wrapper(const std::string &v, const std::string &k);
  static void concrete_set();
};
