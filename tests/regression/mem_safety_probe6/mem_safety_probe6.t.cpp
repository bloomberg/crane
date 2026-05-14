#include <mem_safety_probe6.h>

#include <cassert>
#include <iostream>

int main() {
  using MSP = MemSafetyProbe6;

  auto r1 = MSP::test_tail_adder;
  std::cout << "test_tail_adder = " << r1 << " (expected 102)" << std::endl;
  assert(r1 == 102u);

  auto r2 = MSP::test_head_and_tail;
  std::cout << "test_head_and_tail = " << r2 << " (expected 2)" << std::endl;
  assert(r2 == 2u);

  auto r3 = MSP::test_tail_mapper;
  std::cout << "test_tail_mapper = " << r3 << " (expected 3)" << std::endl;
  assert(r3 == 3u);

  auto r4 = MSP::test_both_subtrees;
  std::cout << "test_both_subtrees = " << r4 << " (expected 40)" << std::endl;
  assert(r4 == 40u);

  auto r5 = MSP::test_chain;
  std::cout << "test_chain = " << r5 << " (expected 63)" << std::endl;
  assert(r5 == 63u);

  auto r6 = MSP::test_capture_reuse;
  std::cout << "test_capture_reuse = " << r6 << " (expected 9)" << std::endl;
  assert(r6 == 9u);

  std::cout << "All mem_safety_probe6 tests passed!" << std::endl;
  return 0;
}
