// Loopification gap (wip): parity's recursive call feeds an if-condition, so
// loopify bails and the generated parity is a plain recursive function.  The
// recursion is still correct; this test pins that behaviour down.
#include "loopify_gap_if_condition.h"

#include <cassert>
#include <iostream>

int main() {
  // parity(n) = n mod 2.
  assert(LoopifyGapIfCondition::parity(0) == 0);
  assert(LoopifyGapIfCondition::parity(1) == 1);
  assert(LoopifyGapIfCondition::parity(4) == 0);
  assert(LoopifyGapIfCondition::parity(5) == 1);
  std::cout << "loopify_gap_if_condition: parity(5) = "
            << LoopifyGapIfCondition::parity(5) << " PASSED" << std::endl;
  return 0;
}
