#include "macro_named_constructor.h"

uint64_t MacroNamedConstructor::code(MacroNamedConstructor::Num n) {
  switch (n) {
  case Num::NAN_: {
    return UINT64_C(1);
  }
  case Num::INFINITY_: {
    return UINT64_C(2);
  }
  case Num::EOF_: {
    return UINT64_C(3);
  }
  case Num::NULL_: {
    return UINT64_C(4);
  }
  case Num::ERRNO: {
    return UINT64_C(5);
  }
  default:
    std::unreachable();
  }
}

/// The standard library's own float_class has a NAN constructor.
bool MacroNamedConstructor::is_normal(double f) {
  switch ([](double _x) {
    const int _c = std::fpclassify(_x);
    const int _n = std::signbit(_x) ? 1 : 0;
    return static_cast<Float_class>(_c == FP_NAN ? 8
                                                 : (_c == FP_INFINITE    ? 6
                                                    : _c == FP_ZERO      ? 4
                                                    : _c == FP_SUBNORMAL ? 2
                                                                         : 0) +
                                                       _n);
  }(f)) {
  case Float_class::PNORMAL: {
    return true;
  }
  default: {
    return false;
  }
  }
}
