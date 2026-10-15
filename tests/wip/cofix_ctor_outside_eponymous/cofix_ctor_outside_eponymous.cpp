#include "cofix_ctor_outside_eponymous.h"

CofixCtorOutsideEponymous::Stream::stream
CofixCtorOutsideEponymous::from(uint64_t n) {
  return Stream::stream::lazy_(
      [=]() -> typename CofixCtorOutsideEponymous::Stream::stream::Scons {
        return {n, from((n + 1))};
      });
}

uint64_t CofixCtorOutsideEponymous::third_of(uint64_t n) {
  return from(n).tl().tl().hd();
}
