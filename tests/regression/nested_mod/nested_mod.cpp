#include "nested_mod.h"

uint64_t
NestedMod::Outer::Inner::area(const NestedMod::Outer::Inner::shape &s) {
  if (std::holds_alternative<typename NestedMod::Outer::Inner::shape::Circle>(
          s.v())) {
    const auto &[a0] =
        std::get<typename NestedMod::Outer::Inner::shape::Circle>(s.v());
    return ((a0 * a0) * UINT64_C(3));
  } else if (std::holds_alternative<
                 typename NestedMod::Outer::Inner::shape::Square>(s.v())) {
    const auto &[a0] =
        std::get<typename NestedMod::Outer::Inner::shape::Square>(s.v());
    return (a0 * a0);
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename NestedMod::Outer::Inner::shape::Triangle>(s.v());
    return (UINT64_C(2) ? (a0 * a1) / UINT64_C(2) : 0);
  }
}

uint64_t NestedMod::Outer::shape_with_color(const Inner::shape &s,
                                            NestedMod::Outer::Color c) {
  switch (c) {
  case Color::RED: {
    return (Inner::area(s) + UINT64_C(100));
  } break;
  case Color::GREEN: {
    return (Inner::area(s) + UINT64_C(200));
  } break;
  case Color::BLUE: {
    return (Inner::area(s) + UINT64_C(300));
  } break;
  default:
    std::unreachable();
  }
}

uint64_t NestedMod::Outer::color_code(NestedMod::Outer::Color c) {
  switch (c) {
  case Color::RED: {
    return UINT64_C(1);
  } break;
  case Color::GREEN: {
    return UINT64_C(2);
  } break;
  case Color::BLUE: {
    return UINT64_C(3);
  } break;
  default:
    std::unreachable();
  }
}
