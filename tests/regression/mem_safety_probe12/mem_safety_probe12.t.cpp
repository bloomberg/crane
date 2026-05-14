#include <mem_safety_probe12.h>

#include <cassert>
#include <iostream>

int main() {
  using MSP = MemSafetyProbe12;

  auto r1 = MSP::test_pack_nat;
  std::cout << "test_pack_nat = " << r1 << " (expected 42)" << std::endl;
  assert(r1 == 42u);

  auto r2 = MSP::test_pack_bool;
  std::cout << "test_pack_bool = " << r2 << " (expected true)" << std::endl;
  assert(r2 == true);

  auto r3 = MSP::test_pack_fn_let;
  std::cout << "test_pack_fn_let = " << r3 << " (expected 15)" << std::endl;
  assert(r3 == 15u);

  // TEST 4: Direct lambda in type-indexed inductive — may crash
  auto r4 = MSP::test_pack_fn_direct;
  std::cout << "test_pack_fn_direct = " << r4 << " (expected 15)" << std::endl;
  assert(r4 == 15u);

  auto r5 = MSP::test_pack_composed;
  std::cout << "test_pack_composed = " << r5 << " (expected 25)" << std::endl;
  assert(r5 == 25u);

  auto r6 = MSP::test_multi_wrap;
  std::cout << "test_multi_wrap = " << r6 << " (expected 30)" << std::endl;
  assert(r6 == 30u);

  auto r7 = MSP::test_wrap_pair;
  std::cout << "test_wrap_pair = " << r7 << " (expected 10)" << std::endl;
  assert(r7 == 10u);

  std::cout << "All mem_safety_probe12 tests passed!" << std::endl;
  return 0;
}
