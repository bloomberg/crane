#include <mem_safety_probe16.h>

#include <cassert>
#include <iostream>

int main() {
  using MSP = MemSafetyProbe16;

  auto r1 = MSP::test_store_closures;
  std::cout << "test_store_closures = " << r1 << " (expected 60)" << std::endl;
  assert(r1 == 60u);

  auto r2 = MSP::test_compose;
  std::cout << "test_compose = " << r2 << " (expected 30)" << std::endl;
  assert(r2 == 30u);

  auto r3 = MSP::test_multi_capture;
  std::cout << "test_multi_capture = " << r3 << " (expected 69)" << std::endl;
  assert(r3 == 69u);

  auto r4 = MSP::test_nested_match;
  std::cout << "test_nested_match = " << r4 << " (expected 40)" << std::endl;
  assert(r4 == 40u);

  auto r5 = MSP::test_pair_closure;
  std::cout << "test_pair_closure = " << r5 << " (expected 350)" << std::endl;
  assert(r5 == 350u);

  auto r6 = MSP::test_deep_nested;
  std::cout << "test_deep_nested = " << r6 << " (expected 31)" << std::endl;
  assert(r6 == 31u);

  auto r7 = MSP::test_zip_apply;
  std::cout << "test_zip_apply = " << r7 << " (expected 33)" << std::endl;
  assert(r7 == 33u);

  auto r8 = MSP::test_tree_map;
  std::cout << "test_tree_map = " << r8 << " (expected 9)" << std::endl;
  assert(r8 == 9u);

  auto r9 = MSP::test_flatten_cps;
  std::cout << "test_flatten_cps = " << r9 << " (expected 6)" << std::endl;
  assert(r9 == 6u);

  std::cout << "All mem_safety_probe16 tests passed!" << std::endl;
  return 0;
}
