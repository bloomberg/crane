#include "macro_named_constructor.h"

uint64_t MacroNamedConstructor::code(MacroNamedConstructor::Num n) {
  switch (n) {
  case Num::NAN: {
    return UINT64_C(1);
  }
  case Num::INFINITY: {
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
  switch (PrimFloat::classify(f)) {
  case Float_class::PNORMAL: {
    return true;
  }
  default: {
    return false;
  }
  }
}

Float_class PrimFloat::classify(double) {
  throw std::logic_error("unrealized axiom: Corelib.Floats.PrimFloat.classify");
}
