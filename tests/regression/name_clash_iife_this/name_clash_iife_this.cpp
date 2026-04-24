#include <name_clash_iife_this.h>

#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
NameClashIifeThis::match_of_match(const NameClashIifeThis::Color c,
                                  const NameClashIifeThis::shape &s) {
  auto &&_sv = [&]() {
    switch (c) {
    case Color::e_RED: {
      return shape::circle(5u);
    }
    case Color::e_GREEN: {
      return shape::square(3u, 4u);
    }
    case Color::e_BLUE: {
      return s;
    }
    default:
      std::unreachable();
    }
  }();
  if (std::holds_alternative<typename NameClashIifeThis::shape::Circle>(
          _sv.v())) {
    const auto &[d_a0] =
        std::get<typename NameClashIifeThis::shape::Circle>(_sv.v());
    return (d_a0 * 2u);
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename NameClashIifeThis::shape::Square>(_sv.v());
    return (d_a0 + d_a1);
  }
}
