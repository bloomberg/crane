#include "cofix_nested_eponymous_undefined.h"

CofixNestedEponymousUndefined::Stream::stream
CofixNestedEponymousUndefined::Stream::from(uint64_t n) {
  return stream::lazy_(
      [=]() -> typename CofixNestedEponymousUndefined::Stream::stream::Scons {
        return {n, from((n + 1))};
      });
}

uint64_t CofixNestedEponymousUndefined::third_of(uint64_t n) {
  return Stream::from(n).tl().tl().hd();
}
