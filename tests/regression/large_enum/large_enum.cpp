#include "large_enum.h"

unsigned int LargeEnum::color_to_nat(LargeEnum::Color c) {
  switch (c) {
  case Color::RED: {
    return 0u;
  }
  case Color::ORANGE: {
    return 1u;
  }
  case Color::YELLOW: {
    return 2u;
  }
  case Color::GREEN: {
    return 3u;
  }
  case Color::BLUE: {
    return 4u;
  }
  case Color::INDIGO: {
    return 5u;
  }
  case Color::VIOLET: {
    return 6u;
  }
  case Color::BLACK: {
    return 7u;
  }
  case Color::WHITE: {
    return 8u;
  }
  case Color::GRAY: {
    return 9u;
  }
  case Color::BROWN: {
    return 10u;
  }
  case Color::PINK: {
    return 11u;
  }
  default:
    std::unreachable();
  }
}

bool LargeEnum::is_warm(LargeEnum::Color c) {
  switch (c) {
  case Color::RED: {
    return true;
  }
  case Color::ORANGE: {
    return true;
  }
  case Color::YELLOW: {
    return true;
  }
  case Color::BROWN: {
    return true;
  }
  case Color::PINK: {
    return true;
  }
  default: {
    return false;
  }
  }
}

bool LargeEnum::is_neutral(LargeEnum::Color c) {
  switch (c) {
  case Color::BLACK: {
    return true;
  }
  case Color::WHITE: {
    return true;
  }
  case Color::GRAY: {
    return true;
  }
  default: {
    return false;
  }
  }
}

unsigned int LargeEnum::tok_to_nat(const LargeEnum::tok &t) {
  if (std::holds_alternative<typename LargeEnum::tok::TNum>(t.v())) {
    const auto &[a0] = std::get<typename LargeEnum::tok::TNum>(t.v());
    return a0;
  } else if (std::holds_alternative<typename LargeEnum::tok::TPlus>(t.v())) {
    return 100u;
  } else if (std::holds_alternative<typename LargeEnum::tok::TMinus>(t.v())) {
    return 101u;
  } else if (std::holds_alternative<typename LargeEnum::tok::TStar>(t.v())) {
    return 102u;
  } else if (std::holds_alternative<typename LargeEnum::tok::TSlash>(t.v())) {
    return 103u;
  } else if (std::holds_alternative<typename LargeEnum::tok::TLParen>(t.v())) {
    return 104u;
  } else if (std::holds_alternative<typename LargeEnum::tok::TRParen>(t.v())) {
    return 105u;
  } else if (std::holds_alternative<typename LargeEnum::tok::TEq>(t.v())) {
    return 106u;
  } else if (std::holds_alternative<typename LargeEnum::tok::TBang>(t.v())) {
    return 107u;
  } else if (std::holds_alternative<typename LargeEnum::tok::TSemicolon>(
                 t.v())) {
    return 108u;
  } else if (std::holds_alternative<typename LargeEnum::tok::TIdent>(t.v())) {
    const auto &[a0] = std::get<typename LargeEnum::tok::TIdent>(t.v());
    return (200u + a0);
  } else {
    return 999u;
  }
}

bool LargeEnum::is_operator(const LargeEnum::tok &t) {
  if (std::holds_alternative<typename LargeEnum::tok::TPlus>(t.v())) {
    return true;
  } else if (std::holds_alternative<typename LargeEnum::tok::TMinus>(t.v())) {
    return true;
  } else if (std::holds_alternative<typename LargeEnum::tok::TStar>(t.v())) {
    return true;
  } else if (std::holds_alternative<typename LargeEnum::tok::TSlash>(t.v())) {
    return true;
  } else {
    return false;
  }
}
