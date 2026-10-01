#ifndef INCLUDED_TEMPLATE_PARAM_REDEF
#define INCLUDED_TEMPLATE_PARAM_REDEF

#include "obj.h"
#include <any>
#include <variant>

enum class Unit;
enum class Unit { TT };

struct Lib {
  template <typename T1 = void>
  static void f(const std::monostate<crane::obj> &_x);
};

struct M {
  template <typename T1 = void>
  static void use(const std::monostate<crane::obj> &x0_) {
    Lib::template f<crane::obj>(x0_);
    return;
  }
};

template <typename T1> void Lib::f(const std::monostate<crane::obj> &) {
  return;
}

#endif // INCLUDED_TEMPLATE_PARAM_REDEF
