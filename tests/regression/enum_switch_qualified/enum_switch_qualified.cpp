#include "enum_switch_qualified.h"

EnumSwitchQualified::Outer::Color
EnumSwitchQualified::Outer::flip(EnumSwitchQualified::Outer::Color c) {
  switch (c) {
  case Color::RED: {
    return Color::BLUE;
  } break;
  case Color::BLUE: {
    return Color::RED;
  } break;
  default:
    std::unreachable();
  }
}

uint64_t EnumSwitchQualified::Outer::code(EnumSwitchQualified::Outer::Color c) {
  switch (c) {
  case Color::RED: {
    return UINT64_C(1);
  } break;
  case Color::BLUE: {
    return UINT64_C(2);
  } break;
  default:
    std::unreachable();
  }
}
