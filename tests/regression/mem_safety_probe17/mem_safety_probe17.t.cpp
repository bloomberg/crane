#include <mem_safety_probe17.h>

#include <cassert>
#include <iostream>

int main() {
  using MSP = MemSafetyProbe17;

  auto r1 = MSP::test_qtree_sum;
  std::cout << "test_qtree_sum = " << r1 << " (expected 20)" << std::endl;
  assert(r1 == 20u);

  auto r2 = MSP::test_qtree_depth;
  std::cout << "test_qtree_depth = " << r2 << " (expected 3)" << std::endl;
  assert(r2 == 3u);

  auto r3 = MSP::test_qtree_mirror;
  std::cout << "test_qtree_mirror = " << r3 << " (expected 14)" << std::endl;
  assert(r3 == 14u);

  auto r4 = MSP::test_qtree_flatten;
  std::cout << "test_qtree_flatten = " << r4 << " (expected 15)" << std::endl;
  assert(r4 == 15u);

  auto r5 = MSP::test_qtree_zip;
  std::cout << "test_qtree_zip = " << r5 << " (expected 30)" << std::endl;
  assert(r5 == 30u);

  auto r6 = MSP::test_weighted;
  std::cout << "test_weighted = " << r6 << " (expected 91)" << std::endl;
  assert(r6 == 91u);

  auto r7 = MSP::test_make_qtree;
  std::cout << "test_make_qtree = " << r7 << " (expected 26)" << std::endl;
  assert(r7 == 26u);

  auto r8 = MSP::test_two_pass_qtree;
  std::cout << "test_two_pass_qtree = " << r8 << " (expected 30)" << std::endl;
  assert(r8 == 30u);

  std::cout << "All mem_safety_probe17 tests passed!" << std::endl;
  return 0;
}
