#include "bake_functor_application_constant.h"

BakeFunctorApplicationConstant::N::t
BakeFunctorApplicationConstant::N::mk(uint64_t n) {
  return ListDef::template repeat<uint64_t>(n, UINT64_C(3));
}

uint64_t BakeFunctorApplicationConstant::N::obs(const List<uint64_t> &x) {
  return x.template fold_left<uint64_t>(
      [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); },
      UINT64_C(0));
}
