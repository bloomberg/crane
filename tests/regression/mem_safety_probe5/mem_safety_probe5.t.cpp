#include <mem_safety_probe5.h>

#include <cassert>
#include <iostream>

int main() {
  using MSP = MemSafetyProbe5;

  auto r1 = MSP::test_sum_left;
  std::cout << "test_sum_left = " << r1 << " (expected 10)" << std::endl;
  assert(r1 == 10u);

  auto r2 = MSP::test_build_apply;
  std::cout << "test_build_apply = " << r2 << " (expected 10)" << std::endl;
  assert(r2 == 10u);

  auto r3 = MSP::test_pair_apply;
  std::cout << "test_pair_apply = " << r3 << " (expected 10)" << std::endl;
  assert(r3 == 10u);

  auto r4 = MSP::test_collect;
  std::cout << "test_collect = " << r4 << " (expected 5)" << std::endl;
  assert(r4 == 5u);

  auto r5 = MSP::test_stress;
  std::cout << "test_stress = " << r5 << " (expected 1275)" << std::endl;
  assert(r5 == 1275u);

  std::cout << "All mem_safety_probe5 tests passed!" << std::endl;
  return 0;
}
