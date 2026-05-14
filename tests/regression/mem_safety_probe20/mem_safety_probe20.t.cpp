#include <mem_safety_probe20.h>

#include <cassert>
#include <iostream>

int main() {
  using MSP = MemSafetyProbe20;

  auto r1 = MSP::test_wrap_if;
  std::cout << "test_wrap_if = " << r1 << " (expected 42)" << std::endl;
  assert(r1 == 42u);

  auto r2 = MSP::test_wrap_match;
  std::cout << "test_wrap_match = " << r2 << " (expected 10)" << std::endl;
  assert(r2 == 10u);

  auto r3 = MSP::test_pair_if;
  std::cout << "test_pair_if = " << r3 << " (expected 30)" << std::endl;
  assert(r3 == 30u);

  auto r4 = MSP::test_wrap_local;
  std::cout << "test_wrap_local = " << r4 << " (expected 25)" << std::endl;
  assert(r4 == 25u);

  auto r5 = MSP::test_double_unwrap;
  std::cout << "test_double_unwrap = " << r5 << " (expected 17)" << std::endl;
  assert(r5 == 17u);

  auto r6 = MSP::test_nested_wrap;
  std::cout << "test_nested_wrap = " << r6 << " (expected 10)" << std::endl;
  assert(r6 == 10u);

  auto r7 = MSP::test_wrap_list;
  std::cout << "test_wrap_list = " << r7 << " (expected 9)" << std::endl;
  assert(r7 == 9u);

  std::cout << "All mem_safety_probe20 tests passed!" << std::endl;
  return 0;
}
