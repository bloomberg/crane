#include <effect_hof_void.h>

#include <cstdlib>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <variant>

/// 7. Use print_endline as a concrete callback
std::string EffectHofVoid::concrete_use() {
  return apply_then_return(
      [](std::string _x0) {
        std::cout << _x0 << '\n';
        return;
      },
      "hello");
}

/// 8. Use set_env as a concrete callback via wrapper
void EffectHofVoid::set_wrapper(const std::string v, const std::string k) {
  setenv(k.c_str(), v.c_str(), 1);
  return;
}

void EffectHofVoid::concrete_set() {
  std::function<void(std::string)> f = [](std::string _x0) {
    set_wrapper("myval", _x0);
    return;
  };
  {
    f("mykey");
    return;
  }
}
