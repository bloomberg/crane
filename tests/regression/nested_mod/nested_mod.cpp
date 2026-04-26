#include <nested_mod.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
NestedMod::Outer::Inner::area(const NestedMod::Outer::Inner::shape &s) {
  if (std::holds_alternative<typename NestedMod::Outer::Inner::shape::Circle>(
          s.v())) {
    const auto &[d_a0] =
        std::get<typename NestedMod::Outer::Inner::shape::Circle>(s.v());
    return ((d_a0 * d_a0) * 3u);
  } else if (std::holds_alternative<
                 typename NestedMod::Outer::Inner::shape::Square>(s.v())) {
    const auto &[d_a0] =
        std::get<typename NestedMod::Outer::Inner::shape::Square>(s.v());
    return (d_a0 * d_a0);
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename NestedMod::Outer::Inner::shape::Triangle>(s.v());
    return (2u ? (d_a0 * d_a1) / 2u : 0);
  }
}

__attribute__((pure)) unsigned int
NestedMod::Outer::shape_with_color(const Inner::shape &s,
                                   const NestedMod::Outer::Color c) {
  switch (c) {
  case Color::e_RED: {
    return (Inner::area(s) + 100u);
  }
  case Color::e_GREEN: {
    return (Inner::area(s) + 200u);
  }
  case Color::e_BLUE: {
    return (Inner::area(s) + 300u);
  }
  default:
    std::unreachable();
  }
}

__attribute__((pure)) unsigned int
NestedMod::Outer::color_code(const NestedMod::Outer::Color c) {
  switch (c) {
  case Color::e_RED: {
    return 1u;
  }
  case Color::e_GREEN: {
    return 2u;
  }
  case Color::e_BLUE: {
    return 3u;
  }
  default:
    std::unreachable();
  }
}
