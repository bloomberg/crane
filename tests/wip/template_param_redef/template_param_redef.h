#ifndef INCLUDED_TEMPLATE_PARAM_REDEF
#define INCLUDED_TEMPLATE_PARAM_REDEF

#include <variant>

enum class Unit { TT };

struct Lib {
  template <typename T1 = void> static void f(const std::monostate &_x);
};

struct M {
  template <typename T1 = void> static void use(const std::monostate &_x0) {
    Lib::template f<T1>(_x0);
    return;
  }
};

template <typename T1 = void> void Lib::f(const std::monostate &) { return; }

#endif // INCLUDED_TEMPLATE_PARAM_REDEF
