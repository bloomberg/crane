#include <mem_safety_probe22.h>

#include <cassert>
#include <iostream>

int main() {
  using MSP = MemSafetyProbe22;

  auto r1 = MSP::test_sum_and_rebuild;
  std::cout << "test_sum_and_rebuild = " << r1 << " (expected 8)" << std::endl;
  assert(r1 == 8u);

  auto r2 = MSP::test_double_tree;
  std::cout << "test_double_tree = " << r2 << " (expected 30)" << std::endl;
  assert(r2 == 30u);

  auto r3 = MSP::test_weighted_sum;
  std::cout << "test_weighted_sum = " << r3 << " (expected 25)" << std::endl;
  assert(r3 == 25u);

  auto r4 = MSP::test_split_sum;
  std::cout << "test_split_sum = " << r4 << " (expected 22)" << std::endl;
  assert(r4 == 22u);

  auto r5 = MSP::test_tree_map;
  std::cout << "test_tree_map = " << r5 << " (expected 36)" << std::endl;
  assert(r5 == 36u);

  auto r6 = MSP::test_mirror;
  std::cout << "test_mirror = " << r6 << " (expected 6)" << std::endl;
  assert(r6 == 6u);

  auto r7 = MSP::test_insert;
  std::cout << "test_insert = " << r7 << " (expected 25)" << std::endl;
  assert(r7 == 25u);

  auto r8 = MSP::test_label_depth;
  std::cout << "test_label_depth = " << r8 << " (expected 5)" << std::endl;
  assert(r8 == 5u);

  std::cout << "All mem_safety_probe22 tests passed!" << std::endl;
  return 0;
}
