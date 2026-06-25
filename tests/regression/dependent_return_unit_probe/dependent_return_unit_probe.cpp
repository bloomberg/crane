#include "dependent_return_unit_probe.h"

std::any DependentReturnUnitProbe::dep(Bool0 b) {
  switch (b) {
  case Bool0::TRUE_: {
    return Unit::TT;
  }
  case Bool0::FALSE_: {
    return Bool0::FALSE_;
  }
  default:
    std::unreachable();
  }
}
