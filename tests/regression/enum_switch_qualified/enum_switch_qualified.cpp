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

uint64_t EnumSwitchQualified::Outer::code(EnumSwitchQualified::Outer::Color c) {
  switch (c) {
  case Color::RED: {
    return UINT64_C(1);
  }
  case Color::BLUE: {
    return UINT64_C(2);
  }
  default:
    std::unreachable();
  }
}
