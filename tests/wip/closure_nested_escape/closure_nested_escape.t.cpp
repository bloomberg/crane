#include <closure_nested_escape.h>

#include <cassert>
#include <iostream>

int main() {
  using CNE = ClosureNestedEscape;

  // test1: make_pair_fix(5): add(3)=8, mul(3)=15, total=23.
  // BUG: both fixpoints capture n by [&], dangles after return.
  auto r1 = CNE::test1;
  std::cout << "test1 = " << r1 << " (expected 23)" << std::endl;
  assert(r1 == 23u);

  // test2: make_pair_fix(7): add(0)=7, mul(4)=28, total=35.
  auto r2 = CNE::test2;
  std::cout << "test2 = " << r2 << " (expected 35)" << std::endl;
  assert(r2 == 35u);

  // test3: make_pair_fix(3): mul(10) = 30.
  auto r3 = CNE::test3;
  std::cout << "test3 = " << r3 << " (expected 30)" << std::endl;
  assert(r3 == 30u);

  std::cout << "All closure_nested_escape tests passed!" << std::endl;
  return 0;
}
