#include "SeparateExtraction.h"

namespace SeparateExtraction {

uint64_t sep_add(uint64_t _x0, uint64_t _x1) { return (_x0 + _x1); }

uint64_t color_to_nat(Color c) {
  switch (c) {
  case Color::RED: {
    return UINT64_C(1);
  } break;
  case Color::GREEN: {
    return UINT64_C(2);
  } break;
  case Color::BLUE: {
    return UINT64_C(3);
  } break;
  default:
    std::unreachable();
  }
}

} // namespace SeparateExtraction
