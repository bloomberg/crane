#include <closure_recursive_build.h>

#include <cassert>
#include <iostream>

int main() {
  using CRB = ClosureRecursiveBuild;

  // test1: build_adders(3) -> [adder_3, adder_2, adder_1].
  // apply_first picks adder_3, calls adder_3(10) = 3+10 = 13.
  // BUG: adder_3 captures n=3 by [&] from a destroyed stack frame.
  auto r1 = CRB::test1;
  std::cout << "test1 = " << r1 << " (expected 13)" << std::endl;
  assert(r1 == 13u);

  // test2: sum all adders applied to 0.
  // adder_3(0) + adder_2(0) + adder_1(0) = 3 + 2 + 1 = 6.
  auto r2 = CRB::test2;
  std::cout << "test2 = " << r2 << " (expected 6)" << std::endl;
  assert(r2 == 6u);

  // test3: noise between build and use -> 5 + 264 = 269.
  auto r3 = CRB::test3;
  std::cout << "test3 = " << r3 << " (expected 269)" << std::endl;
  assert(r3 == 269u);

  std::cout << "All closure_recursive_build tests passed!" << std::endl;
  return 0;
}
