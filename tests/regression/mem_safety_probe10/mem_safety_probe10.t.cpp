#include <mem_safety_probe10.h>

#include <cassert>
#include <iostream>

int main() {
  using MSP = MemSafetyProbe10;

  auto r1 = MSP::test_tree_adder;
  std::cout << "test_tree_adder = " << r1 << " (expected 65)" << std::endl;
  assert(r1 == 65u);

  auto r2 = MSP::test_chain;
  std::cout << "test_chain = " << r2 << " (expected 67)" << std::endl;
  assert(r2 == 67u);

  auto r3 = MSP::test_collect_adders;
  std::cout << "test_collect_adders = " << r3 << " (expected 35)" << std::endl;
  assert(r3 == 35u);

  auto r4 = MSP::test_choose;
  std::cout << "test_choose = " << r4 << " (expected 78)" << std::endl;
  assert(r4 == 78u);

  auto r5 = MSP::test_nested;
  std::cout << "test_nested = " << r5 << " (expected 40)" << std::endl;
  assert(r5 == 40u);

  auto r6 = MSP::test_pair_fn;
  std::cout << "test_pair_fn = " << r6 << " (expected 35)" << std::endl;
  assert(r6 == 35u);

  auto r7 = MSP::test_tree_fns;
  std::cout << "test_tree_fns = " << r7 << " (expected 24)" << std::endl;
  assert(r7 == 24u);

  auto r8 = MSP::test_tree_capture;
  std::cout << "test_tree_capture = " << r8 << " (expected 600)" << std::endl;
  assert(r8 == 600u);

  std::cout << "All mem_safety_probe10 tests passed!" << std::endl;
  return 0;
}
