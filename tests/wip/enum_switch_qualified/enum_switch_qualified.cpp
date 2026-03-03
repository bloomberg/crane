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

color EnumSwitchQualified::Outer::flip(const color c) {
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

unsigned int EnumSwitchQualified::Outer::code(const color c) {
  return [&](void) {
    switch (c) {
    case color::Red: {
      return (0 + 1);
    }
    case color::Blue: {
      return ((0 + 1) + 1);
    }
    }
  }();
}
