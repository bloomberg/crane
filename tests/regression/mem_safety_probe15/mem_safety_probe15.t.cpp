#include <mem_safety_probe15.h>

#include <cassert>
#include <iostream>

int main() {
  using MSP = MemSafetyProbe15;

  auto r1 = MSP::test_flatten;
  std::cout << "test_flatten = " << r1 << " (expected 28)" << std::endl;
  assert(r1 == 28u);

  auto r2 = MSP::test_subtree_sums;
  std::cout << "test_subtree_sums = " << r2 << " (expected 35)" << std::endl;
  assert(r2 == 35u);

  auto r3 = MSP::test_mirror;
  std::cout << "test_mirror = " << r3 << " (expected 10)" << std::endl;
  assert(r3 == 10u);

  auto r4 = MSP::test_zip;
  std::cout << "test_zip = " << r4 << " (expected 40)" << std::endl;
  assert(r4 == 40u);

  auto r5 = MSP::test_deep_spine;
  std::cout << "test_deep_spine = " << r5 << " (expected 5050)" << std::endl;
  assert(r5 == 5050u);

  auto r6 = MSP::test_rev;
  std::cout << "test_rev = " << r6 << " (expected 10)" << std::endl;
  assert(r6 == 10u);

  auto r7 = MSP::test_two_pass;
  std::cout << "test_two_pass = " << r7 << " (expected 56)" << std::endl;
  assert(r7 == 56u);

  auto r8 = MSP::test_map;
  std::cout << "test_map = " << r8 << " (expected 63)" << std::endl;
  assert(r8 == 63u);

  auto r9 = MSP::test_large_tree;
  std::cout << "test_large_tree = " << r9 << " (expected 120)" << std::endl;
  assert(r9 == 120u);

  std::cout << "All mem_safety_probe15 tests passed!" << std::endl;
  return 0;
}
