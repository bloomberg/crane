// A mutual group of functions returning nothing, loopified: it runs in
// constant C++ stack, so ten million steps do not overflow it.
#include "loopify_mutual_void.h"

#include <iostream>

int main() {
  using M = LoopifyMutualVoid;
  M::even_void(0);
  M::odd_void(7);
  M::even_void(10000000);
  M::odd_void(10000001);
  std::cout << "loopify_mutual_void: PASSED" << std::endl;
  return 0;
}
