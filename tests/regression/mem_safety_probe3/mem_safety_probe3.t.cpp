#include <mem_safety_probe3.h>

#include <cassert>
#include <iostream>

int main() {
  using MSP = MemSafetyProbe3;

  auto r1 = MSP::local_fix_capture;
  std::cout << "local_fix_capture = " << r1 << " (expected 171)" << std::endl;
  assert(r1 == 171u);

  auto r2 = MSP::fix_with_closure;
  std::cout << "fix_with_closure = " << r2 << " (expected 80)" << std::endl;
  assert(r2 == 80u);

  auto r3 = MSP::test_paired_closures;
  std::cout << "test_paired_closures = " << r3 << " (expected 40)" << std::endl;
  assert(r3 == 40u);

  auto r4 = MSP::test_tree_sum;
  std::cout << "test_tree_sum = " << r4 << " (expected 60)" << std::endl;
  assert(r4 == 60u);

  auto r5 = MSP::test_mutual_use;
  std::cout << "test_mutual_use = " << r5 << " (expected 80)" << std::endl;
  assert(r5 == 80u);

  auto r6 = MSP::test_nested_pair;
  std::cout << "test_nested_pair = " << r6 << " (expected 104)" << std::endl;
  assert(r6 == 104u);

  auto r7 = MSP::test_map_with_captured;
  std::cout << "test_map_with_captured = " << r7 << " (expected 330)" << std::endl;
  assert(r7 == 330u);

  auto r8 = MSP::test_chain_three;
  std::cout << "test_chain_three = " << r8 << " (expected 60)" << std::endl;
  assert(r8 == 60u);

  auto r9 = MSP::test_opt_pair;
  std::cout << "test_opt_pair = " << r9 << " (expected 94)" << std::endl;
  assert(r9 == 94u);

  auto r10 = MSP::test_deep_tree;
  std::cout << "test_deep_tree = " << r10 << " (expected 5050)" << std::endl;
  assert(r10 == 5050u);

  auto r11 = MSP::test_apply_n;
  std::cout << "test_apply_n = " << r11 << " (expected 50)" << std::endl;
  assert(r11 == 50u);

  auto r12 = MSP::test_partial_fix;
  std::cout << "test_partial_fix = " << r12 << " (expected 40)" << std::endl;
  assert(r12 == 40u);

  std::cout << "All mem_safety_probe3 tests passed!" << std::endl;
  return 0;
}
