#include "enum_switch_qualified.h"

EnumSwitchQualified::Outer::Color
EnumSwitchQualified::Outer::flip(EnumSwitchQualified::Outer::Color c) {
  switch (c) {
  case Color::RED: {
    return Color::BLUE;
  }
  case Color::BLUE: {
    return Color::RED;
  }
  default:
    std::unreachable();
  }
}

unsigned int
EnumSwitchQualified::Outer::code(EnumSwitchQualified::Outer::Color c) {
  switch (c) {
  case Color::RED: {
    return 1u;
  }
  case Color::BLUE: {
    return 2u;
  }
  default:
    std::unreachable();
  }
}
