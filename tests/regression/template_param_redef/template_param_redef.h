#pragma once

#include <type_traits>
#include <variant>

enum class Unit;
enum class Unit { TT };

struct Lib {
  template <typename T1>
  static void f(std::conditional_t<true, std::monostate, T1> _x);
};

struct M {
  template <typename T1>
  static void use(std::conditional_t<true, std::monostate, T1> x0_) {
    Lib::template f<T1>(x0_);
  }
};

template <typename T1>
void Lib::f(std::conditional_t<true, std::monostate, T1>) {}
