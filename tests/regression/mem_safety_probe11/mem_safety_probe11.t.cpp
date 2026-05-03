#include <mem_safety_probe11.h>

#include <cassert>
#include <iostream>

int main() {
  using MSP = MemSafetyProbe11;

  auto r1 = MSP::test_dual_capture;
  std::cout << "test_dual_capture = " << r1 << " (expected 60)" << std::endl;
  assert(r1 == 60u);

  auto r2 = MSP::test_capture_tails;
  std::cout << "test_capture_tails = " << r2 << " (expected 603)" << std::endl;
  assert(r2 == 603u);

  auto r3 = MSP::test_triple_use;
  std::cout << "test_triple_use = " << r3 << " (expected 14)" << std::endl;
  assert(r3 == 14u);

  auto r4 = MSP::test_nested_capture;
  std::cout << "test_nested_capture = " << r4 << " (expected 72)" << std::endl;
  assert(r4 == 72u);

  auto r5 = MSP::test_dual_accum;
  std::cout << "test_dual_accum = " << r5 << " (expected 100)" << std::endl;
  assert(r5 == 100u);

  auto r6 = MSP::test_tree_transformer;
  std::cout << "test_tree_transformer = " << r6 << " (expected 130)" << std::endl;
  assert(r6 == 130u);

  std::cout << "All mem_safety_probe11 tests passed!" << std::endl;
  return 0;
}
