#include <mem_safety_probe23.h>

#include <cassert>
#include <iostream>

int main() {
  using MSP = MemSafetyProbe23;

  auto r1 = MSP::test_sum_with_original;
  std::cout << "test_sum_with_original = " << r1 << " (expected 42)" << std::endl;
  assert(r1 == 42u);

  auto r2 = MSP::test_dup_and_double;
  std::cout << "test_dup_and_double = " << r2 << " (expected 45)" << std::endl;
  assert(r2 == 45u);

  auto r3 = MSP::test_collect_children;
  std::cout << "test_collect_children = " << r3 << " (expected 25)" << std::endl;
  assert(r3 == 25u);

  auto r4 = MSP::test_sum_with_acc;
  std::cout << "test_sum_with_acc = " << r4 << " (expected 12)" << std::endl;
  assert(r4 == 12u);

  auto r5 = MSP::test_interleaved_ops;
  std::cout << "test_interleaved_ops = " << r5 << " (expected 20)" << std::endl;
  assert(r5 == 20u);

  auto r6 = MSP::test_flatten_tree_of_trees;
  std::cout << "test_flatten_tree_of_trees = " << r6 << " (expected 48)" << std::endl;
  assert(r6 == 48u);

  auto r7 = MSP::test_mixed_recurse;
  std::cout << "test_mixed_recurse = " << r7 << " (expected 10)" << std::endl;
  assert(r7 == 10u);

  auto r8 = MSP::test_annotate_sizes;
  std::cout << "test_annotate_sizes = " << r8 << " (expected 73)" << std::endl;
  assert(r8 == 73u);

  std::cout << "All mem_safety_probe23 tests passed!" << std::endl;
  return 0;
}
