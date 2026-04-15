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
  if (std::holds_alternative<typename LargeEnum::tok::TNum>(t->v())) {
    const auto &_m = *std::get_if<typename LargeEnum::tok::TNum>(&t->v());
    return _m.d_a0;
  } else if (std::holds_alternative<typename LargeEnum::tok::TPlus>(t->v())) {
    return 100u;
  } else if (std::holds_alternative<typename LargeEnum::tok::TMinus>(t->v())) {
    return 101u;
  } else if (std::holds_alternative<typename LargeEnum::tok::TStar>(t->v())) {
    return 102u;
  } else if (std::holds_alternative<typename LargeEnum::tok::TSlash>(t->v())) {
    return 103u;
  } else if (std::holds_alternative<typename LargeEnum::tok::TLParen>(t->v())) {
    return 104u;
  } else if (std::holds_alternative<typename LargeEnum::tok::TRParen>(t->v())) {
    return 105u;
  } else if (std::holds_alternative<typename LargeEnum::tok::TEq>(t->v())) {
    return 106u;
  } else if (std::holds_alternative<typename LargeEnum::tok::TBang>(t->v())) {
    return 107u;
  } else if (std::holds_alternative<typename LargeEnum::tok::TSemicolon>(
                 t->v())) {
    return 108u;
  } else if (std::holds_alternative<typename LargeEnum::tok::TIdent>(t->v())) {
    const auto &_m = *std::get_if<typename LargeEnum::tok::TIdent>(&t->v());
    return (200u + _m.d_a0);
  } else {
    return 999u;
  }
}

__attribute__((pure)) bool
LargeEnum::is_operator(const std::shared_ptr<LargeEnum::tok> &t) {
  if (std::holds_alternative<typename LargeEnum::tok::TPlus>(t->v())) {
    return true;
  } else if (std::holds_alternative<typename LargeEnum::tok::TMinus>(t->v())) {
    return true;
  } else if (std::holds_alternative<typename LargeEnum::tok::TStar>(t->v())) {
    return true;
  } else if (std::holds_alternative<typename LargeEnum::tok::TSlash>(t->v())) {
    return true;
  } else {
    return false;
  }
}
