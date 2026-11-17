// rose_sum folds over a rose tree's children with a nested fix that calls the
// outer rose_sum.  The nested fixpoint is adopted as a second entry point of
// rose_sum's frame machine, so both recursions share one stack and the
// generated rose_sum is iterative: no C++ self-call.
#include "loopify_gap_nested_fix.h"

#include <cassert>
#include <iostream>

int main() {
  // sample_tree = Rose 1 [Rose 2 []; Rose 3 [Rose 4 []]]; sum = 1+2+3+4 = 10.
  auto total = LoopifyGapNestedFix::rose_sum_sample();
  assert(total == 10);
  std::cout << "loopify_gap_nested_fix: rose_sum(sample) = " << total
            << " PASSED" << std::endl;
  return 0;
}
