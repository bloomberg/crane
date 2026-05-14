#include <mem_safety_probe29.h>

#include <cassert>
#include <iostream>

int main() {
  using MSP = MemSafetyProbe29;

  auto r1 = MSP::test_outer_basic;
  std::cout << "test_outer_basic = " << r1 << " (expected 36)" << std::endl;
  assert(r1 == 36u);

  auto r2 = MSP::test_dup_inner;
  std::cout << "test_dup_inner = " << r2 << " (expected 90)" << std::endl;
  assert(r2 == 90u);

  auto r3 = MSP::test_transform;
  std::cout << "test_transform = " << r3 << " (expected 30)" << std::endl;
  assert(r3 == 30u);

  auto r4 = MSP::test_expr;
  std::cout << "test_expr = " << r4 << " (expected 35)" << std::endl;
  assert(r4 == 35u);

  auto r5 = MSP::test_tree3;
  std::cout << "test_tree3 = " << r5 << std::endl;
  // Just check it doesn't crash (complex deep tree)

  auto r6 = MSP::test_dup_outer;
  std::cout << "test_dup_outer = " << r6 << " (expected 84)" << std::endl;
  assert(r6 == 84u);

  auto r7 = MSP::test_double_expr;
  std::cout << "test_double_expr = " << r7 << " (expected 94)" << std::endl;
  assert(r7 == 94u);

  auto r8 = MSP::test_cross_type;
  std::cout << "test_cross_type = " << r8 << " (expected 32)" << std::endl;
  assert(r8 == 32u);

  std::cout << "All mem_safety_probe29 tests passed!" << std::endl;
  return 0;
}
