#include "SeparateExtraction.h"

namespace SeparateExtraction {

unsigned int sep_add(unsigned int _x0, unsigned int _x1) { return (_x0 + _x1); }

unsigned int color_to_nat(Color c) {
  switch (c) {
  case Color::RED: {
    return 1u;
  }
  case Color::GREEN: {
    return 2u;
  }
  case Color::BLUE: {
    return 3u;
  }
  default:
    std::unreachable();
  }
}

} // namespace SeparateExtraction
