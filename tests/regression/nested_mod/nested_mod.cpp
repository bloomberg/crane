#include "nested_mod.h"

unsigned int
NestedMod::Outer::Inner::area(const NestedMod::Outer::Inner::shape &s) {
  if (std::holds_alternative<typename NestedMod::Outer::Inner::shape::Circle>(
          s.v())) {
    const auto &[a0] =
        std::get<typename NestedMod::Outer::Inner::shape::Circle>(s.v());
    return ((a0 * a0) * 3u);
  } else if (std::holds_alternative<
                 typename NestedMod::Outer::Inner::shape::Square>(s.v())) {
    const auto &[a0] =
        std::get<typename NestedMod::Outer::Inner::shape::Square>(s.v());
    return (a0 * a0);
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename NestedMod::Outer::Inner::shape::Triangle>(s.v());
    return (2u ? (a0 * a1) / 2u : 0);
  }
}

unsigned int NestedMod::Outer::shape_with_color(const Inner::shape &s,
                                                NestedMod::Outer::Color c) {
  switch (c) {
  case Color::RED: {
    return (Inner::area(s) + 100u);
  }
  case Color::GREEN: {
    return (Inner::area(s) + 200u);
  }
  case Color::BLUE: {
    return (Inner::area(s) + 300u);
  }
  default:
    std::unreachable();
  }
}

unsigned int NestedMod::Outer::color_code(NestedMod::Outer::Color c) {
  switch (c) {
  case Color::RED: {
    return 1u;
  }
  case Color::GREEN: {
    return 2u;
  }
  case Color::BLUE: {
    return 3u;
  }
  default:
    std::unreachable();
  }
}
