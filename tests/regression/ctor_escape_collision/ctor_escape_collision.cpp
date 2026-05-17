#include "ctor_escape_collision.h"

unsigned int CtorEscapeCollision::tag(CtorEscapeCollision::Item x) {
  switch (x) {
  case Item::D_: {
    return 1u;
  }
  case Item::D_0: {
    return 2u;
  }
  case Item::D__: {
    return 3u;
  }
  case Item::D__0: {
    return 4u;
  }
  case Item::D__1: {
    return 5u;
  }
  case Item::D__2: {
    return 6u;
  }
  default:
    std::unreachable();
  }
}
