#include <closure_in_ctor.h>

#include <cassert>
#include <iostream>

int main() {
  using CIC = ClosureInCtor;

  // test1: make_box_fix(5) -> Box(add), add(3) = 5+3 = 8.
  // BUG: local fixpoint captures n by [&], dangles after return.
  auto r1 = CIC::test1;
  std::cout << "test1 = " << r1 << " (expected 8)" << std::endl;
  assert(r1 == 8u);

  // test2: make_box_fix(42), noise, then add(10) = 42+10 = 52.
  auto r2 = CIC::test2;
  std::cout << "test2 = " << r2 << " (expected 52)" << std::endl;
  assert(r2 == 52u);

  // test3: Two boxes, add_10(0) + add_20(0) = 10 + 20 = 30.
  auto r3 = CIC::test3;
  std::cout << "test3 = " << r3 << " (expected 30)" << std::endl;
  assert(r3 == 30u);

  std::cout << "All closure_in_ctor tests passed!" << std::endl;
  return 0;
}
