#include <fix_fold_escape.h>

#include <cassert>
#include <iostream>

int main() {
  using FFE = FixFoldEscape;

  // test1: collect_adders [10,20,30] -> [adder_30, adder_20, adder_10].
  // apply_head = adder_30(5) = 30+5 = 35.
  // BUG: adder captures fold callback parameter by [&], dangles after return.
  auto r1 = FFE::test1;
  std::cout << "test1 = " << r1 << " (expected 35)" << std::endl;
  assert(r1 == 35u);

  // test2: sum all adders at 0 = 30+20+10 = 60.
  auto r2 = FFE::test2;
  std::cout << "test2 = " << r2 << " (expected 60)" << std::endl;
  assert(r2 == 60u);

  // test3: collect [100,200], noise=132, adder_200(0)=200 + 132=332.
  auto r3 = FFE::test3;
  std::cout << "test3 = " << r3 << " (expected 332)" << std::endl;
  assert(r3 == 332u);

  std::cout << "All fix_fold_escape tests passed!" << std::endl;
  return 0;
}
