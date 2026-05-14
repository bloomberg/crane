#include <mem_safety_probe8.h>

#include <cassert>
#include <iostream>

int main() {
  using MSP = MemSafetyProbe8;

  auto r1 = MSP::test_tree_sum;
  std::cout << "test_tree_sum = " << r1 << " (expected 60)" << std::endl;
  assert(r1 == 60u);

  auto r2 = MSP::test_tree_weighted;
  std::cout << "test_tree_weighted = " << r2 << " (expected 100)" << std::endl;
  assert(r2 == 100u);

  auto r3 = MSP::test_deep_tree;
  std::cout << "test_deep_tree = " << r3 << " (expected 5050)" << std::endl;
  assert(r3 == 5050u);

  auto r4 = MSP::test_collect;
  std::cout << "test_collect = " << r4 << " (expected 105)" << std::endl;
  assert(r4 == 105u);

  auto r5 = MSP::test_flatten;
  std::cout << "test_flatten = " << r5 << " (expected 30)" << std::endl;
  assert(r5 == 30u);

  auto r6 = MSP::test_fold_size;
  std::cout << "test_fold_size = " << r6 << " (expected 4)" << std::endl;
  assert(r6 == 4u);

  std::cout << "All mem_safety_probe8 tests passed!" << std::endl;
  return 0;
}
