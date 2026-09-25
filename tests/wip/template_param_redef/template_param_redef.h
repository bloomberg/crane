#ifndef INCLUDED_TEMPLATE_PARAM_REDEF
#define INCLUDED_TEMPLATE_PARAM_REDEF

#include <any>
#include <variant>

enum class Unit;
enum class Unit { TT };

struct Lib {
  template <typename T1 = void>
  static void f(const std::monostate<std::any> &_x);
};

struct M {
  template <typename T1 = void>
  static void use(const std::monostate<std::any> &x0_) {
    Lib::template f<std::any>(x0_);
    return;
  }
};

template <typename T1> void Lib::f(const std::monostate<std::any> &) { return; }

#endif // INCLUDED_TEMPLATE_PARAM_REDEF
