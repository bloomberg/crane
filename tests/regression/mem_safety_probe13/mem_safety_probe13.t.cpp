#include <mem_safety_probe13.h>

#include <cassert>
#include <iostream>

int main() {
  using MSP = MemSafetyProbe13;

  auto r1 = MSP::test_vals_and_fns;
  std::cout << "test_vals_and_fns = " << r1 << " (expected 35)" << std::endl;
  assert(r1 == 35u);

  auto r3 = MSP::test_double_match;
  std::cout << "test_double_match = " << r3 << " (expected 26)" << std::endl;
  assert(r3 == 26u);

  auto r4 = MSP::test_depth_fns;
  std::cout << "test_depth_fns = " << r4 << " (expected 29)" << std::endl;
  assert(r4 == 29u);

  auto r5 = MSP::test_ftree;
  std::cout << "test_ftree = " << r5 << " (expected 321)" << std::endl;
  assert(r5 == 321u);

  auto r6 = MSP::test_flatten_fns;
  std::cout << "test_flatten_fns = " << r6 << " (expected 24)" << std::endl;
  assert(r6 == 24u);

  std::cout << "All mem_safety_probe13 tests passed!" << std::endl;
  return 0;
}
