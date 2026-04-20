#include <fix_in_record.h>

#include <cassert>
#include <iostream>

int main() {
  using FIR = FixInRecord;

  // test1: n=10, base=30, add(7) = 30+7 = 37.
  // BUG: fixpoint in record field captures 'base' by [&], dangles.
  auto r1 = FIR::test1;
  std::cout << "test1 = " << r1 << " (expected 37)" << std::endl;
  assert(r1 == 37u);

  // test2: n=20, base=60, add(15) = 60+15 = 75.
  auto r2 = FIR::test2;
  std::cout << "test2 = " << r2 << " (expected 75)" << std::endl;
  assert(r2 == 75u);

  // test3: n=5, base=15, label=15, fn(0)=15, total=30.
  auto r3 = FIR::test3;
  std::cout << "test3 = " << r3 << " (expected 30)" << std::endl;
  assert(r3 == 30u);

  std::cout << "All fix_in_record tests passed!" << std::endl;
  return 0;
}
