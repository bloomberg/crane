#include <mem_safety_probe26.h>

#include <cassert>
#include <iostream>

int main() {
  using MSP = MemSafetyProbe26;

  auto r1 = MSP::test_match_to_pair;
  std::cout << "test_match_to_pair = " << r1 << " (expected 121)" << std::endl;
  assert(r1 == 121u);

  auto r2 = MSP::test_split_closures;
  std::cout << "test_split_closures = " << r2 << " (expected 328)" << std::endl;
  assert(r2 == 328u);

  auto r3 = MSP::test_match_to_option;
  std::cout << "test_match_to_option = " << r3 << " (expected 115)" << std::endl;
  assert(r3 == 115u);

  auto r4 = MSP::test_build_tree_closures;
  std::cout << "test_build_tree_closures = " << r4 << " (expected 119)" << std::endl;
  assert(r4 == 119u);

  auto r5 = MSP::test_closure_and_sum;
  std::cout << "test_closure_and_sum = " << r5 << " (expected 124)" << std::endl;
  assert(r5 == 124u);

  auto r6 = MSP::test_deep_closure_pair;
  std::cout << "test_deep_closure_pair = " << r6 << " (expected 116)" << std::endl;
  assert(r6 == 116u);

  auto r7 = MSP::test_shared_child_closure;
  std::cout << "test_shared_child_closure = " << r7 << " (expected 110)" << std::endl;
  assert(r7 == 110u);

  auto r8 = MSP::test_conditional_closure;
  std::cout << "test_conditional_closure = " << r8 << " (expected 328)" << std::endl;
  assert(r8 == 328u);

  std::cout << "All mem_safety_probe26 tests passed!" << std::endl;
  return 0;
}
