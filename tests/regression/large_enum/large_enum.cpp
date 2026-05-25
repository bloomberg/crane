#include "large_enum.h"

uint64_t LargeEnum::color_to_nat(LargeEnum::Color c) {
  switch (c) {
  case Color::RED: {
    return UINT64_C(0);
  } break;
  case Color::ORANGE: {
    return UINT64_C(1);
  } break;
  case Color::YELLOW: {
    return UINT64_C(2);
  } break;
  case Color::GREEN: {
    return UINT64_C(3);
  } break;
  case Color::BLUE: {
    return UINT64_C(4);
  } break;
  case Color::INDIGO: {
    return UINT64_C(5);
  } break;
  case Color::VIOLET: {
    return UINT64_C(6);
  } break;
  case Color::BLACK: {
    return UINT64_C(7);
  } break;
  case Color::WHITE: {
    return UINT64_C(8);
  } break;
  case Color::GRAY: {
    return UINT64_C(9);
  } break;
  case Color::BROWN: {
    return UINT64_C(10);
  } break;
  case Color::PINK: {
    return UINT64_C(11);
  } break;
  default:
    std::unreachable();
  }
}

bool LargeEnum::is_warm(LargeEnum::Color c) {
  switch (c) {
  case Color::RED: {
    return true;
  } break;
  case Color::ORANGE: {
    return true;
  } break;
  case Color::YELLOW: {
    return true;
  } break;
  case Color::BROWN: {
    return true;
  } break;
  case Color::PINK: {
    return true;
  } break;
  default: {
    return false;
  }
  }
}

bool LargeEnum::is_neutral(LargeEnum::Color c) {
  switch (c) {
  case Color::BLACK: {
    return true;
  } break;
  case Color::WHITE: {
    return true;
  } break;
  case Color::GRAY: {
    return true;
  } break;
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
