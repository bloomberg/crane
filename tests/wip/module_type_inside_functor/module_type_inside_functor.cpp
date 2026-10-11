#include "module_type_inside_functor.h"

uint64_t ModuleTypeInsideFunctor::F1::f(uint64_t n) {
  return (n + UINT64_C(1));
}
