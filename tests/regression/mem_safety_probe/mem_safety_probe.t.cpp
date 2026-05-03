#include <mem_safety_probe.h>

#include <cassert>
#include <iostream>

int main() {
  using MSP = MemSafetyProbe;

  // TEST 1: HOF calling closure multiple times
  auto r1 = MSP::test_hof_double;
  std::cout << "test_hof_double = " << r1 << " (expected 120)" << std::endl;
  assert(r1 == 120u);

  // TEST 2: Build list of closures and apply them
  auto r2 = MSP::test_closure_list;
  std::cout << "test_closure_list = " << r2 << " (expected 75)" << std::endl;
  assert(r2 == 75u);

  // TEST 3: Closure in pair construction
  auto r3 = MSP::test_pair_closures;
  std::cout << "test_pair_closures = " << r3 << " (expected 152)" << std::endl;
  assert(r3 == 152u);

  // TEST 4: Fold composing closures over trees
  auto r4 = MSP::test_fold_compose;
  std::cout << "test_fold_compose = " << r4 << " (expected 35)" << std::endl;
  assert(r4 == 35u);

  // TEST 5: Partial app + match scrutinee reuse
  auto r5 = MSP::test_match_partial;
  std::cout << "test_match_partial = " << r5 << " (expected 80)" << std::endl;
  assert(r5 == 80u);

  // TEST 6: Deep currying chain
  auto r6 = MSP::test_deep_curry;
  std::cout << "test_deep_curry = " << r6 << " (expected 60)" << std::endl;
  assert(r6 == 60u);

  // TEST 7: Box storing closure, applied twice
  auto r7 = MSP::test_box_apply_twice;
  std::cout << "test_box_apply_twice = " << r7 << " (expected 219)" << std::endl;
  assert(r7 == 219u);

  // TEST 8: Dual capture of same value
  auto r8 = MSP::test_dual_capture;
  std::cout << "test_dual_capture = " << r8 << " (expected 87)" << std::endl;
  assert(r8 == 87u);

  // TEST 9: Map tree with closure
  auto r9 = MSP::test_map_tree;
  std::cout << "test_map_tree = " << r9 << " (expected 63)" << std::endl;
  assert(r9 == 63u);

  // TEST 10: Box from match - closure captures match-bound variable
  auto r10 = MSP::test_box_from_match;
  std::cout << "test_box_from_match = " << r10 << " (expected 15)" << std::endl;
  assert(r10 == 15u);

  // TEST 11: Combine trees - closure captures two different trees
  auto r11 = MSP::test_combine;
  std::cout << "test_combine = " << r11 << " (expected 40)" << std::endl;
  assert(r11 == 40u);

  // TEST 12: Chain of partial applications
  auto r12 = MSP::test_chain_partial;
  std::cout << "test_chain_partial = " << r12 << " (expected 360)" << std::endl;
  assert(r12 == 360u);

  std::cout << "All mem_safety_probe tests passed!" << std::endl;
  return 0;
}
