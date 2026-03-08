#include <algorithm>
#include <any>
#include <cassert>
#include <ctor_escape_collision.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int CtorEscapeCollision::tag(const CtorEscapeCollision::item x) {
  return [&](void) {
    switch (x) {
    case item::D_: {
      return 1u;
    }
    case item::D_0: {
      return 2u;
    }
    case item::D__: {
      return 3u;
    }
    case item::D__0: {
      return 4u;
    }
    case item::D__1: {
      return 5u;
    }
    case item::D__2: {
      return 6u;
    }
    }
  }();
}
