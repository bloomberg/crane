// Nat.even_EvenT calls itself through a coercion of its callee.  Loopified,
// it runs in constant C++ stack; calling itself, half(4000000) would run four
// million frames deep and overflow it.
#include "loopify_coerced_self_call.h"

#include <cassert>
#include <iostream>

int main() {
  using M = LoopifyCoercedSelfCall;
  assert(M::half(0) == 0);
  assert(M::half(10) == 5);
  assert(M::half(4000000) == 2000000);
  std::cout << "loopify_coerced_self_call: half(4000000)=" << M::half(4000000) << " PASSED"
            << std::endl;
  return 0;
}
