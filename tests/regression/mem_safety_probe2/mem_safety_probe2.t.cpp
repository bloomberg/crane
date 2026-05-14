#include <mem_safety_probe2.h>

#include <cassert>
#include <iostream>

int main() {
  using MSP = MemSafetyProbe2;

  // TEST 1: Value type used in both partial app and constructor
  auto r1 = MSP::test_dup_tree;
  std::cout << "test_dup_tree = " << r1 << " (expected 84)" << std::endl;
  assert(r1 == 84u);

  // TEST 2: CPS-style continuation
  auto r2 = MSP::test_cps;
  std::cout << "test_cps = " << r2 << " (expected 125)" << std::endl;
  assert(r2 == 125u);

  // TEST 3: Compose two closures
  auto r3 = MSP::test_compose;
  std::cout << "test_compose = " << r3 << " (expected 35)" << std::endl;
  assert(r3 == 35u);

  // TEST 4: Partial application of constructor wrapper
  auto r4 = MSP::test_partial_ctor;
  std::cout << "test_partial_ctor = " << r4 << " (expected 42)" << std::endl;
  assert(r4 == 42u);

  // TEST 5: Closure capturing a closure
  auto r5 = MSP::test_double_wrap;
  std::cout << "test_double_wrap = " << r5 << " (expected 62)" << std::endl;
  assert(r5 == 62u);

  // TEST 6: Value type used twice in pair
  auto r6 = MSP::test_tree_pair;
  std::cout << "test_tree_pair = " << r6 << " (expected 120)" << std::endl;
  assert(r6 == 120u);

  // TEST 7: Closures escape through a list
  auto r7 = MSP::test_closure_escape_list;
  std::cout << "test_closure_escape_list = " << r7 << " (expected 40)" << std::endl;
  assert(r7 == 40u);

  // TEST 8: Match with partial apps on destructured fields
  auto r8 = MSP::test_extract_apply;
  std::cout << "test_extract_apply = " << r8 << " (expected 80)" << std::endl;
  assert(r8 == 80u);

  // TEST 9: Option wrapping a closure
  auto r9 = MSP::test_opt_closure;
  std::cout << "test_opt_closure = " << r9 << " (expected 52)" << std::endl;
  assert(r9 == 52u);

  // TEST 10: Two partial apps with different captured values
  auto r10 = MSP::test_two_partial;
  std::cout << "test_two_partial = " << r10 << " (expected 30)" << std::endl;
  assert(r10 == 30u);

  // TEST 11a: Branch use true
  auto r11a = MSP::test_branch_true;
  std::cout << "test_branch_true = " << r11a << " (expected 60)" << std::endl;
  assert(r11a == 60u);

  // TEST 11b: Branch use false
  auto r11b = MSP::test_branch_false;
  std::cout << "test_branch_false = " << r11b << " (expected 160)" << std::endl;
  assert(r11b == 160u);

  // TEST 12: Clone and close
  auto r12 = MSP::test_clone_close;
  std::cout << "test_clone_close = " << r12 << " (expected 87)" << std::endl;
  assert(r12 == 87u);

  // TEST 13: Fold building tree from closures
  auto r13 = MSP::test_fold_tree;
  std::cout << "test_fold_tree = " << r13 << " (expected 35)" << std::endl;
  assert(r13 == 35u);

  // TEST 14: Pair of closure and tree
  auto r14 = MSP::test_pair_closure_tree;
  std::cout << "test_pair_closure_tree = " << r14 << " (expected 125)" << std::endl;
  assert(r14 == 125u);

  // TEST 15: Chain of closures applied in sequence
  auto r15 = MSP::test_chain;
  std::cout << "test_chain = " << r15 << " (expected 65)" << std::endl;
  assert(r15 == 65u);

  // TEST 16: Closure captures match-bound field
  auto r16 = MSP::test_capture_branch;
  std::cout << "test_capture_branch = " << r16 << " (expected 80)" << std::endl;
  assert(r16 == 80u);

  // TEST 17: Reverse list of closures and apply
  auto r17 = MSP::test_rev_closures;
  std::cout << "test_rev_closures = " << r17 << " (expected 75)" << std::endl;
  assert(r17 == 75u);

  // TEST 18: Build tree from partial app results
  auto r18 = MSP::test_build_from_partial;
  std::cout << "test_build_from_partial = " << r18 << " (expected 180)" << std::endl;
  assert(r18 == 180u);

  std::cout << "All mem_safety_probe2 tests passed!" << std::endl;
  return 0;
}
