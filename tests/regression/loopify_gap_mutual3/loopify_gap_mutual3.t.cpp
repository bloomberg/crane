// A three-way mutual recursion (rot_a -> rot_b -> rot_c -> rot_a).  Loopify now
// inlines the whole cycle and turns all three into while-loops (it used to only
// handle 2-way cycles).  This test guards the result stays correct.
#include "loopify_gap_mutual3.h"

#include <cassert>
#include <iostream>

int main() {
  // The cycle has period 3: rot_a(n) walks a->b->c->a decrementing n.
  assert(LoopifyGapMutual3::rot_a(0) == 0);
  assert(LoopifyGapMutual3::rot_b(0) == 1);
  assert(LoopifyGapMutual3::rot_c(0) == 2);
  assert(LoopifyGapMutual3::rot_a(5) == 2);
  assert(LoopifyGapMutual3::rot_b(5) == 0);
  assert(LoopifyGapMutual3::rot_c(5) == 1);
  std::cout << "loopify_gap_mutual3: rot_a(5)=" << LoopifyGapMutual3::rot_a(5)
            << " rot_b(5)=" << LoopifyGapMutual3::rot_b(5)
            << " rot_c(5)=" << LoopifyGapMutual3::rot_c(5) << " PASSED"
            << std::endl;
  return 0;
}
