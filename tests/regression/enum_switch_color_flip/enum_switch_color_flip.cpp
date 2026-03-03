#include <algorithm>
#include <any>
#include <cassert>
#include <enum_switch_color_flip.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

EnumSwitchColorFlip::Outer::color
EnumSwitchColorFlip::Outer::flip(const EnumSwitchColorFlip::Outer::color c) {
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
EnumSwitchColorFlip::Outer::code(const EnumSwitchColorFlip::Outer::color c) {
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
