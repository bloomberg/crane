#include "name_clash_iife_this.h"

uint64_t NameClashIifeThis::match_of_match(NameClashIifeThis::Color c,
                                           const NameClashIifeThis::shape &s) {
  auto &&_sv = [&]() {
    switch (c) {
    case Color::RED: {
      return shape::circle(UINT64_C(5));
    }
    case Color::GREEN: {
      return shape::square(UINT64_C(3), UINT64_C(4));
    }
    case Color::BLUE: {
      return s;
    }
    default:
      std::unreachable();
    }
  }();
  if (std::holds_alternative<typename NameClashIifeThis::shape::Circle>(
          _sv.v())) {
    const auto &[a0] =
        std::get<typename NameClashIifeThis::shape::Circle>(_sv.v());
    return (a0 * UINT64_C(2));
  } else {
    const auto &[a0, a1] =
        std::get<typename NameClashIifeThis::shape::Square>(_sv.v());
    return (a0 + a1);
  }
}
