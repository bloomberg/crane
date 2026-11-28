#include <id_mapped_option_shape.h>

#include <cassert>

int main() {
  using M = IdMappedOptionShape;
  assert(M::m == 4);
  return 0;
}
