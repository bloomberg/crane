// Loopification gap (wip): Ackermann recurses with an inner result as the
// argument of an outer recursive call (ack m' (ack_n n')).  That outer call is
// not in a linearisable position, so the generated ack keeps a recursive
// self-call.  The recursion is still correct; this test pins that behaviour.
#include "loopify_gap_ackermann.h"

#include <cassert>
#include <iostream>

int main() {
  // Standard Ackermann values.
  assert(LoopifyGapAckermann::ack(0, 0) == 1);
  assert(LoopifyGapAckermann::ack(1, 1) == 3);
  assert(LoopifyGapAckermann::ack(2, 3) == 9);
  assert(LoopifyGapAckermann::ack(3, 3) == 61);
  std::cout << "loopify_gap_ackermann: ack(3,3) = "
            << LoopifyGapAckermann::ack(3, 3) << " PASSED" << std::endl;
  return 0;
}
