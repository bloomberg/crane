#include <enum_switch_qualified.h>

#include <type_traits>

__attribute__((pure)) EnumSwitchQualified::Outer::Color
EnumSwitchQualified::Outer::flip(const EnumSwitchQualified::Outer::Color c) {
  return [&](void) {
    switch (c) {
    case Color::e_RED: {
      return Color::e_BLUE;
    }
    case Color::e_BLUE: {
      return Color::e_RED;
    }
    }
  }();
}

__attribute__((pure)) unsigned int
EnumSwitchQualified::Outer::code(const EnumSwitchQualified::Outer::Color c) {
  return [&](void) {
    switch (c) {
    case Color::e_RED: {
      return 1u;
    }
    case Color::e_BLUE: {
      return 2u;
    }
    }
  }();
}
