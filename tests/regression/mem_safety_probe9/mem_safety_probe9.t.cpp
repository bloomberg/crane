#include <mem_safety_probe9.h>

#include <cassert>
#include <iostream>

int main() {
  using MSP = MemSafetyProbe9;

  auto r1 = MSP::test_collect;
  std::cout << "test_collect = " << r1 << " (expected 110)" << std::endl;
  assert(r1 == 110u);

  auto r2 = MSP::test_left_sums;
  std::cout << "test_left_sums = " << r2 << " (expected 13)" << std::endl;
  assert(r2 == 13u);

  auto r3 = MSP::test_list_accum;
  std::cout << "test_list_accum = " << r3 << " (expected 40)" << std::endl;
  assert(r3 == 40u);

  auto r4 = MSP::test_triple;
  std::cout << "test_triple = " << r4 << " (expected 100)" << std::endl;
  assert(r4 == 100u);

  auto r5 = MSP::test_cross;
  std::cout << "test_cross = " << r5 << " (expected 45)" << std::endl;
  assert(r5 == 45u);

  auto r6 = MSP::test_stress;
  std::cout << "test_stress = " << r6 << std::endl;

  std::cout << "All mem_safety_probe9 tests passed!" << std::endl;
  return 0;
}
