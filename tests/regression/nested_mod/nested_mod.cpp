#include <nested_mod.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int NestedMod::Outer::Inner::area(
    const std::shared_ptr<NestedMod::Outer::Inner::shape> &s) {
  return std::visit(
      Overloaded{
          [](const typename NestedMod::Outer::Inner::shape::Circle &_args)
              -> unsigned int { return ((_args.d_a0 * _args.d_a0) * 3u); },
          [](const typename NestedMod::Outer::Inner::shape::Square &_args)
              -> unsigned int { return (_args.d_a0 * _args.d_a0); },
          [](const typename NestedMod::Outer::Inner::shape::Triangle &_args)
              -> unsigned int {
            return (2u ? (_args.d_a0 * _args.d_a1) / 2u : 0);
          }},
      s->v());
}

__attribute__((pure)) unsigned int
NestedMod::Outer::shape_with_color(const std::shared_ptr<Inner::shape> &s,
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
