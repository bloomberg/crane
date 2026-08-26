#include <non_uniform_pair_nest.h>
#include <cassert>
#include <iostream>
int main() {
  auto r = NonUniformPairNest::go;
  std::cout << "go = " << r << " (want 2)" << std::endl;
  assert(r == 2);
  return 0;
}
