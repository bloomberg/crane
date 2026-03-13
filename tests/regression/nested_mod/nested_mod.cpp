#include <nested_mod.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int NestedMod::Outer::Inner::area(
    const std::shared_ptr<NestedMod::Outer::Inner::shape> &s) {
  return std::visit(
      Overloaded{
          [](const typename NestedMod::Outer::Inner::shape::Circle _args)
              -> unsigned int {
            unsigned int r = _args.d_a0;
            return ((r * r) * 3u);
          },
          [](const typename NestedMod::Outer::Inner::shape::Square _args)
              -> unsigned int {
            unsigned int side = _args.d_a0;
            return (side * side);
          },
          [](const typename NestedMod::Outer::Inner::shape::Triangle _args)
              -> unsigned int {
            unsigned int a = _args.d_a0;
            unsigned int b = _args.d_a1;
            return Nat::div((std::move(a) * std::move(b)), 2u);
          }},
      s->v());
}

__attribute__((pure)) unsigned int
NestedMod::Outer::shape_with_color(const std::shared_ptr<Inner::shape> &s,
                                   const NestedMod::Outer::Color c) {
  return [&](void) {
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
    }
  }();
}

__attribute__((pure)) unsigned int
NestedMod::Outer::color_code(const NestedMod::Outer::Color c) {
  return [&](void) {
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
    }
  }();
}

__attribute__((pure)) std::pair<unsigned int, unsigned int>
Nat::divmod(const unsigned int x, const unsigned int y, const unsigned int q,
            const unsigned int u) {
  if (x <= 0) {
    return std::make_pair(std::move(q), std::move(u));
  } else {
    unsigned int x_ = x - 1;
    if (u <= 0) {
      return Nat::divmod(std::move(x_), y, (q + 1), y);
    } else {
      unsigned int u_ = u - 1;
      return Nat::divmod(std::move(x_), y, q, std::move(u_));
    }
  }
}

__attribute__((pure)) unsigned int Nat::div(const unsigned int x,
                                            const unsigned int y) {
  if (y <= 0) {
    return std::move(y);
  } else {
    unsigned int y_ = y - 1;
    return Nat::divmod(x, y_, 0u, y_).first;
  }
}
