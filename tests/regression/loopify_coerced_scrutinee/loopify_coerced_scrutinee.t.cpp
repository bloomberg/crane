// A loopified type-indexed evaluator whose conditionals match a recursive
// call through a coercion to bool.
#include "loopify_coerced_scrutinee.h"

#include <cassert>
#include <iostream>

int main() {
  using M = LoopifyCoercedScrutinee;
  assert(M::deep == 7);
  assert(M::chosen == 3);
  std::cout << "loopify_coerced_scrutinee: deep=" << M::deep << " chosen=" << M::chosen
            << " PASSED" << std::endl;
  return 0;
}
