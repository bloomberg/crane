#include <inductive_in_module.h>

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

__attribute__((pure)) unsigned int InductiveInModule::Inner::color_to_nat(
    const InductiveInModule::Inner::Color c) {
  return [&](void) {
    switch (c) {
    case Color::e_RED: {
      return 0u;
    }
    case Color::e_GREEN: {
      return 1u;
    }
    case Color::e_BLUE: {
      return 2u;
    }
    }
  }();
}
