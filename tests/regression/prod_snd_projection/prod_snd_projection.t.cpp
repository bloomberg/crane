#include <prod_snd_projection.h>
#include <cassert>
#include <iostream>
int main() {
  std::cout << "go = " << ProdSndProjection::go << " (want 2)" << std::endl;
  assert(ProdSndProjection::go == 2);
  return 0;
}
