#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <ram_accessor_namespace_safe.h>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int
RamAccessorNamespaceSafe::read(const RamAccessorNamespaceSafe::port x) {
  return [&](void) {
    switch (x) {
    case port::ReadPort: {
      return (((0 + 1) + 1) + 1);
    }
    case port::WritePort: {
      return ((((0 + 1) + 1) + 1) + 1);
    }
    }
  }();
}
