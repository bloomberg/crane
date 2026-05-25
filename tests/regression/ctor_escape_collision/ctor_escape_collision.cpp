#include "ctor_escape_collision.h"

uint64_t CtorEscapeCollision::tag(CtorEscapeCollision::Item x) {
  switch (x) {
  case Item::D_: {
    return UINT64_C(1);
  } break;
  case Item::D_0: {
    return UINT64_C(2);
  } break;
  case Item::D__: {
    return UINT64_C(3);
  } break;
  case Item::D__0: {
    return UINT64_C(4);
  } break;
  case Item::D__1: {
    return UINT64_C(5);
  } break;
  case Item::D__2: {
    return UINT64_C(6);
  } break;
  default:
    std::unreachable();
  }
}
