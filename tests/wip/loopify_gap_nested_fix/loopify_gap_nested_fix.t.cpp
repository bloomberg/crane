// Loopification gap (wip): rose_sum folds over children with a nested fix that
// calls the outer rose_sum.  An inner fixpoint calling the outer function can't
// share its frame stack, so that call is left as explicit C++ recursion.  The
// recursion is still correct; this test pins that behaviour down.
#include "loopify_gap_nested_fix.h"

#include <cassert>
#include <iostream>

int main() {
  // sample_tree = Rose 1 [Rose 2 []; Rose 3 [Rose 4 []]]; sum = 1+2+3+4 = 10.
  auto total = LoopifyGapNestedFix::rose_sum_sample({});
  assert(total == 10);
  std::cout << "loopify_gap_nested_fix: rose_sum(sample) = " << total
            << " PASSED" << std::endl;
  return 0;
}
