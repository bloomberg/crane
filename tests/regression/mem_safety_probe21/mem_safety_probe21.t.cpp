#include <mem_safety_probe21.h>

#include <cassert>
#include <iostream>

int main() {
  using MSP = MemSafetyProbe21;

  auto r1 = MSP::test_grow_and_sum;
  std::cout << "test_grow_and_sum = " << r1 << " (expected 6)" << std::endl;
  assert(r1 == 6u);

  auto r2 = MSP::test_double_grow;
  std::cout << "test_double_grow = " << r2 << " (expected 15)" << std::endl;
  assert(r2 == 15u);

  auto r3 = MSP::test_branch_grow;
  std::cout << "test_branch_grow = " << r3 << " (expected 14)" << std::endl;
  assert(r3 == 14u);

  auto r4 = MSP::test_embed_grow;
  std::cout << "test_embed_grow = " << r4 << " (expected 10)" << std::endl;
  assert(r4 == 10u);

  auto r5 = MSP::test_accum_tree;
  std::cout << "test_accum_tree = " << r5 << " (expected 10)" << std::endl;
  assert(r5 == 10u);

  auto r6 = MSP::test_cps_sum;
  std::cout << "test_cps_sum = " << r6 << " (expected 6)" << std::endl;
  assert(r6 == 6u);

  auto r7 = MSP::test_weave;
  std::cout << "test_weave = " << r7 << " (expected 9)" << std::endl;
  assert(r7 == 9u);

  auto r8 = MSP::test_sum_and_grow;
  std::cout << "test_sum_and_grow = " << r8 << " (expected 15)" << std::endl;
  assert(r8 == 15u);

  std::cout << "All mem_safety_probe21 tests passed!" << std::endl;
  return 0;
}
