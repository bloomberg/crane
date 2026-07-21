// Loopification gap (wip): swap_pair's non-tail recursive call is destructured
// and consumed, so loopify leaves it as a plain recursive function.  The
// recursion is still correct; this test pins that behaviour down.
#include "loopify_gap_pair_destructure.h"

#include <cassert>
#include <iostream>
#include <utility>

int main() {
  // swap_pair(0)=(0,0); swap_pair(S m) = (snd, fst+1) of swap_pair(m).
  auto p0 = LoopifyGapPairDestructure::swap_pair(0);
  assert(p0.first == 0 && p0.second == 0);
  auto p5 = LoopifyGapPairDestructure::swap_pair(5);
  assert(p5.first == 2 && p5.second == 3);
  std::cout << "loopify_gap_pair_destructure: swap_pair(5) = (" << p5.first
            << ", " << p5.second << ") PASSED" << std::endl;
  return 0;
}
