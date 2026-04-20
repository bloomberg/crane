#include <closure_pair_this.h>

#include <cassert>
#include <iostream>

int main() {
  using CPT = ClosurePairThis;

  // test1: pair of closures on temporary tree (sum=7), flag=0.
  // fst adds tree_sum, snd multiplies by tree_sum.
  // BUG: both closures capture dangling 'this' pointer.
  // Expected: (3+7) + (7*2) = 24.
  auto r1 = CPT::test1;
  std::cout << "test1 = " << r1 << " (expected 24)" << std::endl;
  assert(r1 == 24u);

  // test2: flag=1. fst adds tree_sum, snd is identity.
  // Expected: (7+4) + 5 = 16.
  auto r2 = CPT::test2;
  std::cout << "test2 = " << r2 << " (expected 16)" << std::endl;
  assert(r2 == 16u);

  // test3: Extra allocation between closure creation and use.
  // Expected: 1009 + 10 = 1019.
  auto r3 = CPT::test3;
  std::cout << "test3 = " << r3 << " (expected 1019)" << std::endl;
  assert(r3 == 1019u);

  std::cout << "All closure_pair_this tests passed!" << std::endl;
  return 0;
}
