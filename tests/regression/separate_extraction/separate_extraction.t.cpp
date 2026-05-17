#include "SeparateExtraction.h"

#include <cassert>

int main() {
  assert(SeparateExtraction::sep_add(3u, 4u) == 7u);
  assert(SeparateExtraction::sep_add(0u, 0u) == 0u);

  assert(SeparateExtraction::color_to_nat(SeparateExtraction::Color::RED) == 1u);
  assert(SeparateExtraction::color_to_nat(SeparateExtraction::Color::GREEN) == 2u);
  assert(SeparateExtraction::color_to_nat(SeparateExtraction::Color::BLUE) == 3u);

  return 0;
}
