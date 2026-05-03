#include <mem_safety_probe25.h>

#include <cassert>
#include <iostream>

int main() {
  using MSP = MemSafetyProbe25;

  auto r1 = MSP::test_make_sum_fn;
  std::cout << "test_make_sum_fn = " << r1 << " (expected 121)" << std::endl;
  assert(r1 == 121u);

  auto r2 = MSP::test_match_closure;
  std::cout << "test_match_closure = " << r2 << " (expected 121)" << std::endl;
  assert(r2 == 121u);

  auto r3 = MSP::test_pair_closures;
  std::cout << "test_pair_closures = " << r3 << " (expected 314)" << std::endl;
  assert(r3 == 314u);

  auto r4 = MSP::test_nested_match_closure;
  std::cout << "test_nested_match_closure = " << r4 << " (expected 116)" << std::endl;
  assert(r4 == 116u);

  auto r5 = MSP::test_deep_match_closure;
  std::cout << "test_deep_match_closure = " << r5 << " (expected 113)" << std::endl;
  assert(r5 == 113u);

  auto r6 = MSP::test_build_adders;
  std::cout << "test_build_adders = " << r6 << " (expected 142)" << std::endl;
  assert(r6 == 142u);

  auto r7 = MSP::test_match_then_pair;
  std::cout << "test_match_then_pair = " << r7 << " (expected 129)" << std::endl;
  assert(r7 == 129u);

  auto r8 = MSP::test_match_closure_opt;
  std::cout << "test_match_closure_opt = " << r8 << " (expected 115)" << std::endl;
  assert(r8 == 115u);

  std::cout << "All mem_safety_probe25 tests passed!" << std::endl;
  return 0;
}
