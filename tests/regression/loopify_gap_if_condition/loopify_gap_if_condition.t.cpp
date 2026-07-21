// parity's recursive call feeds an if-condition.  Loopify hoists it out of the
// condition and produces an explicit-stack loop (it used to bail to plain
// recursion).  This test guards the result stays correct.
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
