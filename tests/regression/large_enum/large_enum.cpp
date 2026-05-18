#include "large_enum.h"

uint64_t LargeEnum::color_to_nat(LargeEnum::Color c) {
  switch (c) {
  case Color::RED: {
    return UINT64_C(0);
  }
  case Color::ORANGE: {
    return UINT64_C(1);
  }
  case Color::YELLOW: {
    return UINT64_C(2);
  }
  case Color::GREEN: {
    return UINT64_C(3);
  }
  case Color::BLUE: {
    return UINT64_C(4);
  }
  case Color::INDIGO: {
    return UINT64_C(5);
  }
  case Color::VIOLET: {
    return UINT64_C(6);
  }
  case Color::BLACK: {
    return UINT64_C(7);
  }
  case Color::WHITE: {
    return UINT64_C(8);
  }
  case Color::GRAY: {
    return UINT64_C(9);
  }
  case Color::BROWN: {
    return UINT64_C(10);
  }
  case Color::PINK: {
    return UINT64_C(11);
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

uint64_t LargeEnum::tok_to_nat(const LargeEnum::tok &t) {
  if (std::holds_alternative<typename LargeEnum::tok::TNum>(t.v())) {
    const auto &[a0] = std::get<typename LargeEnum::tok::TNum>(t.v());
    return a0;
  } else if (std::holds_alternative<typename LargeEnum::tok::TPlus>(t.v())) {
    return UINT64_C(100);
  } else if (std::holds_alternative<typename LargeEnum::tok::TMinus>(t.v())) {
    return UINT64_C(101);
  } else if (std::holds_alternative<typename LargeEnum::tok::TStar>(t.v())) {
    return UINT64_C(102);
  } else if (std::holds_alternative<typename LargeEnum::tok::TSlash>(t.v())) {
    return UINT64_C(103);
  } else if (std::holds_alternative<typename LargeEnum::tok::TLParen>(t.v())) {
    return UINT64_C(104);
  } else if (std::holds_alternative<typename LargeEnum::tok::TRParen>(t.v())) {
    return UINT64_C(105);
  } else if (std::holds_alternative<typename LargeEnum::tok::TEq>(t.v())) {
    return UINT64_C(106);
  } else if (std::holds_alternative<typename LargeEnum::tok::TBang>(t.v())) {
    return UINT64_C(107);
  } else if (std::holds_alternative<typename LargeEnum::tok::TSemicolon>(
                 t.v())) {
    return UINT64_C(108);
  } else if (std::holds_alternative<typename LargeEnum::tok::TIdent>(t.v())) {
    const auto &[a0] = std::get<typename LargeEnum::tok::TIdent>(t.v());
    return (UINT64_C(200) + a0);
  } else {
    return UINT64_C(999);
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
