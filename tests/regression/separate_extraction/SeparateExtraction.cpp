#include <SeparateExtraction.h>

namespace SeparateExtraction {

unsigned int sep_add(const unsigned int _x0, const unsigned int _x1) {
  return (_x0 + _x1);
}

unsigned int color_to_nat(const Color c) {
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

} // namespace SeparateExtraction
