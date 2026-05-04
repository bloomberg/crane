#include <SeparateExtraction.h>

#include <cassert>

int main() {
  assert(SeparateExtraction::sep_add(3u, 4u) == 7u);
  assert(SeparateExtraction::sep_add(0u, 0u) == 0u);

  assert(SeparateExtraction::color_to_nat(SeparateExtraction::Color::e_RED) == 1u);
  assert(SeparateExtraction::color_to_nat(SeparateExtraction::Color::e_GREEN) == 2u);
  assert(SeparateExtraction::color_to_nat(SeparateExtraction::Color::e_BLUE) == 3u);

  return 0;
}
