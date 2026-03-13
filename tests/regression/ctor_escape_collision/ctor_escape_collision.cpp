#include <ctor_escape_collision.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

__attribute__((pure)) unsigned int
CtorEscapeCollision::tag(const CtorEscapeCollision::Item x) {
  return [&](void) {
    switch (x) {
    case Item::e_D_: {
      return 1u;
    }
    case Item::e_D_0: {
      return 2u;
    }
    case Item::e_D__: {
      return 3u;
    }
    case Item::e_D__0: {
      return 4u;
    }
    case Item::e_D__1: {
      return 5u;
    }
    case Item::e_D__2: {
      return 6u;
    }
    }
  }();
}
