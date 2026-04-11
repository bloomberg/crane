#include <large_enum.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
LargeEnum::color_to_nat(const LargeEnum::Color c) {
  switch (c) {
  case Color::e_RED: {
    return 0u;
  }
  case Color::e_ORANGE: {
    return 1u;
  }
  case Color::e_YELLOW: {
    return 2u;
  }
  case Color::e_GREEN: {
    return 3u;
  }
  case Color::e_BLUE: {
    return 4u;
  }
  case Color::e_INDIGO: {
    return 5u;
  }
  case Color::e_VIOLET: {
    return 6u;
  }
  case Color::e_BLACK: {
    return 7u;
  }
  case Color::e_WHITE: {
    return 8u;
  }
  case Color::e_GRAY: {
    return 9u;
  }
  case Color::e_BROWN: {
    return 10u;
  }
  case Color::e_PINK: {
    return 11u;
  }
  default:
    std::unreachable();
  }
}

__attribute__((pure)) bool LargeEnum::is_warm(const LargeEnum::Color c) {
  switch (c) {
  case Color::e_RED: {
    return true;
  }
  case Color::e_ORANGE: {
    return true;
  }
  case Color::e_YELLOW: {
    return true;
  }
  case Color::e_BROWN: {
    return true;
  }
  case Color::e_PINK: {
    return true;
  }
  default: {
    return false;
  }
  }
}

__attribute__((pure)) bool LargeEnum::is_neutral(const LargeEnum::Color c) {
  switch (c) {
  case Color::e_BLACK: {
    return true;
  }
  case Color::e_WHITE: {
    return true;
  }
  case Color::e_GRAY: {
    return true;
  }
  default: {
    return false;
  }
  }
}

__attribute__((pure)) unsigned int
LargeEnum::tok_to_nat(const std::shared_ptr<LargeEnum::tok> &t) {
  return std::visit(
      Overloaded{[](const typename LargeEnum::tok::TNum _args) -> unsigned int {
                   return _args.d_a0;
                 },
                 [](const typename LargeEnum::tok::TPlus) -> unsigned int {
                   return 100u;
                 },
                 [](const typename LargeEnum::tok::TMinus) -> unsigned int {
                   return 101u;
                 },
                 [](const typename LargeEnum::tok::TStar) -> unsigned int {
                   return 102u;
                 },
                 [](const typename LargeEnum::tok::TSlash) -> unsigned int {
                   return 103u;
                 },
                 [](const typename LargeEnum::tok::TLParen) -> unsigned int {
                   return 104u;
                 },
                 [](const typename LargeEnum::tok::TRParen) -> unsigned int {
                   return 105u;
                 },
                 [](const typename LargeEnum::tok::TEq) -> unsigned int {
                   return 106u;
                 },
                 [](const typename LargeEnum::tok::TBang) -> unsigned int {
                   return 107u;
                 },
                 [](const typename LargeEnum::tok::TSemicolon) -> unsigned int {
                   return 108u;
                 },
                 [](const typename LargeEnum::tok::TIdent _args)
                     -> unsigned int { return (200u + _args.d_a0); },
                 [](const typename LargeEnum::tok::TEOF) -> unsigned int {
                   return 999u;
                 }},
      t->v());
}

__attribute__((pure)) bool
LargeEnum::is_operator(const std::shared_ptr<LargeEnum::tok> &t) {
  return std::visit(
      Overloaded{
          [](const typename LargeEnum::tok::TPlus) -> bool { return true; },
          [](const typename LargeEnum::tok::TMinus) -> bool { return true; },
          [](const typename LargeEnum::tok::TStar) -> bool { return true; },
          [](const typename LargeEnum::tok::TSlash) -> bool { return true; },
          [](const auto) -> bool { return false; }},
      t->v());
}
