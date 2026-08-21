#include <loopify_variant_self_assign.h>

#include <cassert>
#include <iostream>

int main() {
  // Rocq: Compute (go 8) = 20, Compute (go 12) = 42.
  auto r8 = LoopifyVariantSelfAssign::go(8u);
  auto r12 = LoopifyVariantSelfAssign::go(12u);
  std::cout << "go 8  = " << r8 << " (want 20)" << std::endl;
  std::cout << "go 12 = " << r12 << " (want 42)" << std::endl;
  assert(r8 == 20u);
  assert(r12 == 42u);
  return 0;
}
