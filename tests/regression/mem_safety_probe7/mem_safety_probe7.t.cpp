#include <mem_safety_probe7.h>

#include <cassert>
#include <iostream>

int main() {
  using MSP = MemSafetyProbe7;

  auto r1 = MSP::test_len_closures;
  std::cout << "test_len_closures = " << r1 << " (expected 6)" << std::endl;
  assert(r1 == 6u);

  auto r2 = MSP::test_sum_closures;
  std::cout << "test_sum_closures = " << r2 << " (expected 80)" << std::endl;
  assert(r2 == 80u);

  auto r3 = MSP::test_tree_closures;
  std::cout << "test_tree_closures = " << r3 << " (expected 40)" << std::endl;
  assert(r3 == 40u);

  auto r4 = MSP::test_accum_closures;
  std::cout << "test_accum_closures = " << r4 << " (expected 14)" << std::endl;
  assert(r4 == 14u);

  auto r5 = MSP::test_subtree_getters;
  std::cout << "test_subtree_getters = " << r5 << " (expected 40)" << std::endl;
  assert(r5 == 40u);

  auto r6 = MSP::test_stress_closures;
  std::cout << "test_stress_closures = " << r6 << " (expected 190)" << std::endl;
  assert(r6 == 190u);

  std::cout << "All mem_safety_probe7 tests passed!" << std::endl;
  return 0;
}
