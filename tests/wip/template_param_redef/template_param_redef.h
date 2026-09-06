#ifndef INCLUDED_TEMPLATE_PARAM_REDEF
#define INCLUDED_TEMPLATE_PARAM_REDEF

#include <variant>

enum class Unit { TT };

struct Lib {
  template <typename T1> static void f(const std::monostate &_x);
};

struct M {
  template <typename T1> static void use(const std::monostate &x0_) {
    Lib::template f<T1>(x0_);
    return;
  }
};

template <typename T1> void Lib::f(const std::monostate &) { return; }

#endif // INCLUDED_TEMPLATE_PARAM_REDEF
