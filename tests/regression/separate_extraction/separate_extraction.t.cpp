#include "SeparateExtraction.h"

#include <cassert>

int main() {
  assert(sep_add(3u, 4u) == 7u);
  assert(sep_add(0u, 0u) == 0u);

  assert(color_to_nat(Color::e_RED) == 1u);
  assert(color_to_nat(Color::e_GREEN) == 2u);
  assert(color_to_nat(Color::e_BLUE) == 3u);

  return 0;
}
