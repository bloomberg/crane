#include <gadt_index_erasure.h>
#include <cassert>
#include <iostream>

int main() {
  std::cout << GadtIndexErasure::run << std::endl;
  assert(GadtIndexErasure::run == 6);
  return 0;
}
