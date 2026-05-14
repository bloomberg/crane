#include <mem_safety_probe28.h>

#include <cassert>
#include <iostream>

int main() {
  using MSP = MemSafetyProbe28;

  auto r1 = MSP::test_zip_trees;
  std::cout << "test_zip_trees = " << r1 << " (expected 166)" << std::endl;
  assert(r1 == 166u);

  auto r2 = MSP::test_zip_depth;
  std::cout << "test_zip_depth = " << r2 << " (expected 4)" << std::endl;
  assert(r2 == 4u);

  auto r3 = MSP::test_zip_and_sum;
  std::cout << "test_zip_and_sum = " << r3 << " (expected 100)" << std::endl;
  assert(r3 == 100u);

  auto r4 = MSP::test_double_zip;
  std::cout << "test_double_zip = " << r4 << " (expected 24)" << std::endl;
  assert(r4 == 24u);

  auto r5 = MSP::test_zip_collect;
  std::cout << "test_zip_collect = " << r5 << " (expected 15)" << std::endl;
  assert(r5 == 15u);

  auto r6 = MSP::test_merge_trees;
  std::cout << "test_merge_trees = " << r6 << " (expected 15)" << std::endl;
  assert(r6 == 15u);

  auto r7 = MSP::test_deep_zip;
  std::cout << "test_deep_zip = " << r7 << std::endl;
  // Just check it doesn't crash

  auto r8 = MSP::test_nested_zip;
  std::cout << "test_nested_zip = " << r8 << " (expected 170)" << std::endl;
  assert(r8 == 170u);

  std::cout << "All mem_safety_probe28 tests passed!" << std::endl;
  return 0;
}
