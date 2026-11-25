#pragma once

#include <type_traits>
#include <variant>

enum class Unit;
enum class Unit { TT };

struct Lib {
  template <typename T1>
  static void f(const std::conditional_t<true, std::monostate, T1> &_x);
};

struct M {
  template <typename T1>
  static void use(const std::conditional_t<true, std::monostate, T1> &x0_) {
    Lib::template f<T1>(x0_);
    return;
  }
};

template <typename T1>
void Lib::f(const std::conditional_t<true, std::monostate, T1> &) {
  return;
}
