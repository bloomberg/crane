#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <large_enum.h>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int LargeEnum::color_to_nat(const LargeEnum::color c) {
  return [&](void) {
    switch (c) {
    case color::Red: {
      return 0u;
    }
    case color::Orange: {
      return 1u;
    }
    case color::Yellow: {
      return 2u;
    }
    case color::Green: {
      return 3u;
    }
    case color::Blue: {
      return 4u;
    }
    case color::Indigo: {
      return 5u;
    }
    case color::Violet: {
      return 6u;
    }
    case color::Black: {
      return 7u;
    }
    case color::White: {
      return 8u;
    }
    case color::Gray: {
      return 9u;
    }
    case color::Brown: {
      return 10u;
    }
    case color::Pink: {
      return 11u;
    }
    }
  }();
}

bool LargeEnum::is_warm(const LargeEnum::color c) {
  return [&](void) {
    switch (c) {
    case color::Red: {
      return true;
    }
    case color::Orange: {
      return true;
    }
    case color::Yellow: {
      return true;
    }
    case color::Green: {
      return false;
    }
    case color::Blue: {
      return false;
    }
    case color::Indigo: {
      return false;
    }
    case color::Violet: {
      return false;
    }
    case color::Black: {
      return false;
    }
    case color::White: {
      return false;
    }
    case color::Gray: {
      return false;
    }
    case color::Brown: {
      return true;
    }
    case color::Pink: {
      return true;
    }
    }
  }();
}

bool LargeEnum::is_neutral(const LargeEnum::color c) {
  return [&](void) {
    switch (c) {
    case color::Red: {
      return false;
    }
    case color::Orange: {
      return false;
    }
    case color::Yellow: {
      return false;
    }
    case color::Green: {
      return false;
    }
    case color::Blue: {
      return false;
    }
    case color::Indigo: {
      return false;
    }
    case color::Violet: {
      return false;
    }
    case color::Black: {
      return true;
    }
    case color::White: {
      return true;
    }
    case color::Gray: {
      return true;
    }
    case color::Brown: {
      return false;
    }
    case color::Pink: {
      return false;
    }
    }
  }();
}

unsigned int LargeEnum::tok_to_nat(const std::shared_ptr<LargeEnum::tok> &t) {
  return std::visit(
      Overloaded{
          [](const typename LargeEnum::tok::TNum _args) -> unsigned int {
            unsigned int n = _args._a0;
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
            unsigned int n = _args._a0;
            return (200u + std::move(n));
          },
          [](const typename LargeEnum::tok::TEOF _args) -> unsigned int {
            return 999u;
          }},
      t->v());
}

bool LargeEnum::is_operator(const std::shared_ptr<LargeEnum::tok> &t) {
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
