#include <mem_safety_probe19.h>

#include <cassert>
#include <iostream>

int main() {
  using MSP = MemSafetyProbe19;

  auto r1 = MSP::test_choose;
  std::cout << "test_choose = " << r1 << " (expected 42)" << std::endl;
  assert(r1 == 42u);

  auto r2 = MSP::test_option_fn;
  std::cout << "test_option_fn = " << r2 << " (expected 18)" << std::endl;
  assert(r2 == 18u);

  auto r3 = MSP::test_choice_left;
  std::cout << "test_choice_left = " << r3 << " (expected 10)" << std::endl;
  assert(r3 == 10u);

  auto r4 = MSP::test_choice_both;
  std::cout << "test_choice_both = " << r4 << " (expected 11)" << std::endl;
  assert(r4 == 11u);

  auto r5 = MSP::test_make_adder;
  std::cout << "test_make_adder = " << r5 << " (expected 25)" << std::endl;
  assert(r5 == 25u);

  auto r6 = MSP::test_double_use;
  std::cout << "test_double_use = " << r6 << " (expected 17)" << std::endl;
  assert(r6 == 17u);

  auto r7 = MSP::test_pass_closure;
  std::cout << "test_pass_closure = " << r7 << " (expected 25)" << std::endl;
  assert(r7 == 25u);

  auto r8 = MSP::test_nested_match;
  std::cout << "test_nested_match = " << r8 << " (expected 4)" << std::endl;
  assert(r8 == 4u);

  auto r9 = MSP::test_nested_match2;
  std::cout << "test_nested_match2 = " << r9 << " (expected 8)" << std::endl;
  assert(r9 == 8u);

  auto r10 = MSP::test_delayed_use;
  std::cout << "test_delayed_use = " << r10 << " (expected 606)" << std::endl;
  assert(r10 == 606u);

  std::cout << "All mem_safety_probe19 tests passed!" << std::endl;
  return 0;
}
