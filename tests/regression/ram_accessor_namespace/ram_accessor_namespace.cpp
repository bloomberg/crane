#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <ram_accessor_namespace.h>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int RamAccessorNamespace::score(const RamAccessorNamespace::item x) {
  return [&](void) {
    switch (x) {
    case item::S_: {
      return (0 + 1);
    }
    case item::S_0: {
      return ((0 + 1) + 1);
    }
    }
  }();
}
