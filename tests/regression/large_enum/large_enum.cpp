#include <large_enum.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

__attribute__((pure)) unsigned int
LargeEnum::color_to_nat(const LargeEnum::Color c) {
  return [&](void) {
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
    }
  }();
}

__attribute__((pure)) bool LargeEnum::is_warm(const LargeEnum::Color c) {
  return [&](void) {
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
    case Color::e_GREEN: {
      return false;
    }
    case Color::e_BLUE: {
      return false;
    }
    case Color::e_INDIGO: {
      return false;
    }
    case Color::e_VIOLET: {
      return false;
    }
    case Color::e_BLACK: {
      return false;
    }
    case Color::e_WHITE: {
      return false;
    }
    case Color::e_GRAY: {
      return false;
    }
    case Color::e_BROWN: {
      return true;
    }
    case Color::e_PINK: {
      return true;
    }
    }
  }();
}

__attribute__((pure)) bool LargeEnum::is_neutral(const LargeEnum::Color c) {
  return [&](void) {
    switch (c) {
    case Color::e_RED: {
      return false;
    }
    case Color::e_ORANGE: {
      return false;
    }
    case Color::e_YELLOW: {
      return false;
    }
    case Color::e_GREEN: {
      return false;
    }
    case Color::e_BLUE: {
      return false;
    }
    case Color::e_INDIGO: {
      return false;
    }
    case Color::e_VIOLET: {
      return false;
    }
    case Color::e_BLACK: {
      return true;
    }
    case Color::e_WHITE: {
      return true;
    }
    case Color::e_GRAY: {
      return true;
    }
    case Color::e_BROWN: {
      return false;
    }
    case Color::e_PINK: {
      return false;
    }
    }
  }();
}

__attribute__((pure)) unsigned int
LargeEnum::tok_to_nat(const std::shared_ptr<LargeEnum::tok> &t) {
  return std::visit(
      Overloaded{
          [](const typename LargeEnum::tok::TNum _args) -> unsigned int {
            unsigned int n = _args.d_a0;
            return std::move(n);
          },
          [](const typename LargeEnum::tok::TPlus _args) -> unsigned int {
            return 100u;
          },
          [](const typename LargeEnum::tok::TMinus _args) -> unsigned int {
            return 101u;
          },
          [](const typename LargeEnum::tok::TStar _args) -> unsigned int {
            return 102u;
          },
          [](const typename LargeEnum::tok::TSlash _args) -> unsigned int {
            return 103u;
          },
          [](const typename LargeEnum::tok::TLParen _args) -> unsigned int {
            return 104u;
          },
          [](const typename LargeEnum::tok::TRParen _args) -> unsigned int {
            return 105u;
          },
          [](const typename LargeEnum::tok::TEq _args) -> unsigned int {
            return 106u;
          },
          [](const typename LargeEnum::tok::TBang _args) -> unsigned int {
            return 107u;
          },
          [](const typename LargeEnum::tok::TSemicolon _args) -> unsigned int {
            return 108u;
          },
          [](const typename LargeEnum::tok::TIdent _args) -> unsigned int {
            unsigned int n = _args.d_a0;
            return (200u + std::move(n));
          },
          [](const typename LargeEnum::tok::TEOF _args) -> unsigned int {
            return 999u;
          }},
      t->v());
}

__attribute__((pure)) bool
LargeEnum::is_operator(const std::shared_ptr<LargeEnum::tok> &t) {
  return std::visit(
      Overloaded{[](const typename LargeEnum::tok::TNum _args) -> bool {
                   return false;
                 },
                 [](const typename LargeEnum::tok::TPlus _args) -> bool {
                   return true;
                 },
                 [](const typename LargeEnum::tok::TMinus _args) -> bool {
                   return true;
                 },
                 [](const typename LargeEnum::tok::TStar _args) -> bool {
                   return true;
                 },
                 [](const typename LargeEnum::tok::TSlash _args) -> bool {
                   return true;
                 },
                 [](const typename LargeEnum::tok::TLParen _args) -> bool {
                   return false;
                 },
                 [](const typename LargeEnum::tok::TRParen _args) -> bool {
                   return false;
                 },
                 [](const typename LargeEnum::tok::TEq _args) -> bool {
                   return false;
                 },
                 [](const typename LargeEnum::tok::TBang _args) -> bool {
                   return false;
                 },
                 [](const typename LargeEnum::tok::TSemicolon _args) -> bool {
                   return false;
                 },
                 [](const typename LargeEnum::tok::TIdent _args) -> bool {
                   return false;
                 },
                 [](const typename LargeEnum::tok::TEOF _args) -> bool {
                   return false;
                 }},
      t->v());
}
