#include <dependent_return_unit_probe.h>

#include <any>
#include <memory>
#include <type_traits>
#include <utility>

std::any DependentReturnUnitProbe::dep(const Bool0 b) {
  switch (b) {
  case Bool0::e_TRUE0: {
    return Unit::e_TT;
  }
  case Bool0::e_FALSE0: {
    return Bool0::e_FALSE0;
  }
  default:
    std::unreachable();
  }
}
