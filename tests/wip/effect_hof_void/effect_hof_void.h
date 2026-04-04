#ifndef INCLUDED_EFFECT_HOF_VOID
#define INCLUDED_EFFECT_HOF_VOID

#include <cstdlib>
#include <functional>
#include <iostream>
#include <optional>
#include <string>
#include <type_traits>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct EffectHofVoid {
  /// 1. Apply a void callback
  template <typename F0> static void apply_void(F0 &&f, const std::string _x0) {
    f(_x0);
    return;
  } /// 2. Apply a void callback then return a value

  template <typename F0>
  static std::string apply_then_return(F0 &&f, const std::string x) {
    f(x);
    return x;
  } /// 3. Apply a value callback

  template <typename F0>
  static std::string apply_value(F0 &&f, const std::string x) {
    return f(x);
  }

  /// 4. Apply callback conditionally
  template <typename F1>
  static void apply_if(const bool flag, F1 &&f, const std::string x) {
    if (flag) {
      f(x);
      return;
    } else {
      return;
    }
  } /// 5. Chain two void callbacks

  template <typename F0, typename F1>
  static void chain_void(F0 &&f, F1 &&g, const std::string x) {
    f(x);
    g(x);
    return;
  } /// 6. Apply a callback N times

  template <typename F0>
  static unsigned int apply_n(F0 &&f, const std::string x,
                              const unsigned int n) {
    if (n <= 0) {
      return 0u;
    } else {
      unsigned int n_ = n - 1;
      f(x);
      unsigned int rest = apply_n(f, x, n_);
      return (rest + 1);
    }
  }

  /// 7. Use print_endline as a concrete callback
  static std::string concrete_use();
  /// 8. Use set_env as a concrete callback via wrapper
  static void set_wrapper(const std::string v, const std::string k);
  static void concrete_set();
};

#endif // INCLUDED_EFFECT_HOF_VOID
