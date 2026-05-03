#include <mem_safety_probe14.h>

#include <cassert>
#include <iostream>

int main() {
  using MSP = MemSafetyProbe14;

  auto r1 = MSP::use_make_adder;
  std::cout << "use_make_adder = " << r1 << " (expected 65)" << std::endl;
  assert(r1 == 65u);

  auto r2 = MSP::test_use_twice;
  std::cout << "test_use_twice = " << r2 << " (expected 60)" << std::endl;
  assert(r2 == 60u);

  auto r3 = MSP::test_closure_consume;
  std::cout << "test_closure_consume = " << r3 << " (expected 40)" << std::endl;
  assert(r3 == 40u);

  auto r4 = MSP::test_two_closures;
  std::cout << "test_two_closures = " << r4 << " (expected 93)" << std::endl;
  assert(r4 == 93u);

  auto r5 = MSP::test_capture_match;
  std::cout << "test_capture_match = " << r5 << " (expected 60)" << std::endl;
  assert(r5 == 60u);

  auto r6 = MSP::test_level_fns;
  std::cout << "test_level_fns = " << r6 << " (expected 235)" << std::endl;
  assert(r6 == 235u);

  auto r7 = MSP::test_fn_and_val;
  std::cout << "test_fn_and_val = " << r7 << " (expected 1205)" << std::endl;
  assert(r7 == 1205u);

  auto r8 = MSP::test_stress;
  std::cout << "test_stress = " << r8 << " (expected 36)" << std::endl;
  assert(r8 == 36u);

  std::cout << "All mem_safety_probe14 tests passed!" << std::endl;
  return 0;
}
