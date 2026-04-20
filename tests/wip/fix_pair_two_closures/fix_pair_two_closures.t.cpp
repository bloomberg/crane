#include <fix_pair_two_closures.h>

#include <cassert>
#include <iostream>

int main() {
  using FPT = FixPairTwoClosures;

  // test1: make_ops(10,20). f(3)+g(5) = 13+25 = 38.
  auto r1 = FPT::test1;
  std::cout << "test1 = " << r1 << " (expected 38)" << std::endl;
  assert(r1 == 38u);

  // test2: interleaved f(1)+g(2)+f(3) = 11+22+13 = 46.
  auto r2 = FPT::test2;
  std::cout << "test2 = " << r2 << " (expected 46)" << std::endl;
  assert(r2 == 46u);

  // test3: f(0)+g(0) = 100+1 = 101.
  auto r3 = FPT::test3;
  std::cout << "test3 = " << r3 << " (expected 101)" << std::endl;
  assert(r3 == 101u);

  std::cout << "All fix_pair_two_closures tests passed!" << std::endl;
  return 0;
}
