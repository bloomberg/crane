#include <mem_safety_probe4.h>

#include <cassert>
#include <iostream>

int main() {
  using MSP = MemSafetyProbe4;

  auto r1 = MSP::test_sum_through;
  std::cout << "test_sum_through = " << r1 << " (expected 60)" << std::endl;
  assert(r1 == 60u);

  auto r2 = MSP::test_add_through;
  std::cout << "test_add_through = " << r2 << " (expected 60)" << std::endl;
  assert(r2 == 60u);

  auto r3 = MSP::test_double_partial;
  std::cout << "test_double_partial = " << r3 << " (expected 60)" << std::endl;
  assert(r3 == 60u);

  auto r4 = MSP::test_weighted_sum;
  std::cout << "test_weighted_sum = " << r4 << " (expected 95)" << std::endl;
  assert(r4 == 95u);

  auto r5 = MSP::test_transform;
  std::cout << "test_transform = " << r5 << " (expected 60)" << std::endl;
  assert(r5 == 60u);

  auto r6 = MSP::test_process_list;
  std::cout << "test_process_list = " << r6 << " (expected 60)" << std::endl;
  assert(r6 == 60u);

  auto r7 = MSP::test_nested_apply;
  std::cout << "test_nested_apply = " << r7 << " (expected 60)" << std::endl;
  assert(r7 == 60u);

  std::cout << "All mem_safety_probe4 tests passed!" << std::endl;
  return 0;
}
