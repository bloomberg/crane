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

unsigned int InductiveInModule::Inner::color_to_nat(
    const InductiveInModule::Inner::color c) {
  return [&](void) {
    switch (c) {
    case color::Red: {
      return 0u;
    }
    case color::Green: {
      return 1u;
    }
    case color::Blue: {
      return 2u;
    }
    }
  }();
}
