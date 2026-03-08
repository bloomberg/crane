#include <algorithm>
#include <any>
#include <cassert>
#include <enum_switch_qualified.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

EnumSwitchQualified::Outer::color
EnumSwitchQualified::Outer::flip(const EnumSwitchQualified::Outer::color c) {
  return [&](void) {
    switch (c) {
    case color::Red: {
      return color::Blue;
    }
    case color::Blue: {
      return color::Red;
    }
    }
  }();
}

unsigned int
EnumSwitchQualified::Outer::code(const EnumSwitchQualified::Outer::color c) {
  return [&](void) {
    switch (c) {
    case color::Red: {
      return 1u;
    }
    case color::Blue: {
      return 2u;
    }
    }
  }();
}
