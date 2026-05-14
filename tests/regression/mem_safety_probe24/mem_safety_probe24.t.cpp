#include <mem_safety_probe24.h>

#include <cassert>
#include <iostream>

int main() {
  using MSP = MemSafetyProbe24;

  auto r1 = MSP::test_self_annotate;
  std::cout << "test_self_annotate = " << r1 << " (expected 10)" << std::endl;
  assert(r1 == 10u);

  auto r2 = MSP::test_pair_self;
  std::cout << "test_pair_self = " << r2 << " (expected 42)" << std::endl;
  assert(r2 == 42u);

  auto r3 = MSP::test_triple_use;
  std::cout << "test_triple_use = " << r3 << " (expected 15)" << std::endl;
  assert(r3 == 15u);

  auto r4 = MSP::test_tag_tree;
  std::cout << "test_tag_tree = " << r4 << " (expected 30)" << std::endl;
  assert(r4 == 30u);

  auto r5 = MSP::test_nested_ops;
  std::cout << "test_nested_ops = " << r5 << " (expected 63)" << std::endl;
  assert(r5 == 63u);

  auto r6 = MSP::test_clone_and_transform;
  std::cout << "test_clone_and_transform = " << r6 << " (expected 24)" << std::endl;
  assert(r6 == 24u);

  auto r7 = MSP::test_list_to_tree;
  std::cout << "test_list_to_tree = " << r7 << " (expected 6)" << std::endl;
  assert(r7 == 6u);

  auto r8 = MSP::test_zip_trees;
  std::cout << "test_zip_trees = " << r8 << " (expected 66)" << std::endl;
  assert(r8 == 66u);

  std::cout << "All mem_safety_probe24 tests passed!" << std::endl;
  return 0;
}
