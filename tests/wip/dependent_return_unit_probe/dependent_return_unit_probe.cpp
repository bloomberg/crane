#include "dependent_return_unit_probe.h"

std::any DependentReturnUnitProbe::dep(Bool0 b) {
  switch (b) {
  case Bool0::e_TRUE: {
    return Unit::e_TT;
  }
  case Bool0::e_FALSE: {
    return Bool0::e_FALSE;
  }
  default:
    std::unreachable();
  }
}
