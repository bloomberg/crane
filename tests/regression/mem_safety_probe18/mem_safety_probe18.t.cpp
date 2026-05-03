#include <mem_safety_probe18.h>

#include <cassert>
#include <iostream>

int main() {
  using MSP = MemSafetyProbe18;

  auto r1 = MSP::test_dup;
  std::cout << "test_dup = " << r1 << " (expected 84)" << std::endl;
  assert(r1 == 84u);

  auto r2 = MSP::test_let_reuse;
  std::cout << "test_let_reuse = " << r2 << " (expected 60)" << std::endl;
  assert(r2 == 60u);

  auto r3 = MSP::test_apply_twice;
  std::cout << "test_apply_twice = " << r3 << " (expected 14)" << std::endl;
  assert(r3 == 14u);

  auto r4 = MSP::test_tree_from_tree;
  std::cout << "test_tree_from_tree = " << r4 << " (expected 15)" << std::endl;
  assert(r4 == 15u);

  auto r5 = MSP::test_fold_tree;
  std::cout << "test_fold_tree = " << r5 << " (expected 6)" << std::endl;
  assert(r5 == 6u);

  auto r6 = MSP::test_concat;
  std::cout << "test_concat = " << r6 << " (expected 21)" << std::endl;
  assert(r6 == 21u);

  auto r7 = MSP::test_chain;
  std::cout << "test_chain = " << r7 << " (expected 20)" << std::endl;
  assert(r7 == 20u);

  auto r8 = MSP::test_build_tree_list;
  std::cout << "test_build_tree_list = " << r8 << " (expected 36)" << std::endl;
  assert(r8 == 36u);

  auto r9 = MSP::test_triple_use;
  std::cout << "test_triple_use = " << r9 << " (expected 28)" << std::endl;
  assert(r9 == 28u);

  std::cout << "All mem_safety_probe18 tests passed!" << std::endl;
  return 0;
}
