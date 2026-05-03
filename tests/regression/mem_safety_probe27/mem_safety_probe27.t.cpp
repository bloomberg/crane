#include <mem_safety_probe27.h>

#include <cassert>
#include <iostream>

int main() {
  using MSP = MemSafetyProbe27;

  auto r1 = MSP::test_pair_with_fn;
  std::cout << "test_pair_with_fn = " << r1 << " (expected 142)" << std::endl;
  assert(r1 == 142u);

  auto r2 = MSP::test_cond_pair_fn;
  std::cout << "test_cond_pair_fn = " << r2 << " (expected 326)" << std::endl;
  assert(r2 == 326u);

  auto r3 = MSP::test_pair_two_trees;
  std::cout << "test_pair_two_trees = " << r3 << " (expected 120)" << std::endl;
  assert(r3 == 120u);

  auto r4 = MSP::test_opt_tree_fn;
  std::cout << "test_opt_tree_fn = " << r4 << " (expected 115)" << std::endl;
  assert(r4 == 115u);

  auto r5 = MSP::test_nested_closure_pair;
  std::cout << "test_nested_closure_pair = " << r5 << " (expected 115)" << std::endl;
  assert(r5 == 115u);

  auto r6 = MSP::test_triple_fns;
  std::cout << "test_triple_fns = " << r6 << " (expected 316)" << std::endl;
  assert(r6 == 316u);

  auto r7 = MSP::test_fn_and_tree;
  std::cout << "test_fn_and_tree = " << r7 << " (expected 114)" << std::endl;
  assert(r7 == 114u);

  auto r8 = MSP::test_wrapped_fn;
  std::cout << "test_wrapped_fn = " << r8 << " (expected 124)" << std::endl;
  assert(r8 == 124u);

  std::cout << "All mem_safety_probe27 tests passed!" << std::endl;
  return 0;
}
