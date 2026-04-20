#include <mutual_fix_escape.h>

#include <cassert>
#include <iostream>

int main() {
  using MFE = MutualFixEscape;

  // test1: even(4)=true(1), odd(3)=true(1). Total=2.
  auto r1 = MFE::test1;
  std::cout << "test1 = " << r1 << " (expected 2)" << std::endl;
  assert(r1 == 2u);

  // test2: even(5)=false(0), odd(6)=false(0). Total=0.
  auto r2 = MFE::test2;
  std::cout << "test2 = " << r2 << " (expected 0)" << std::endl;
  assert(r2 == 0u);

  // test3: count_even(0)=10, count_even(3)=23. Total=33.
  auto r3 = MFE::test3;
  std::cout << "test3 = " << r3 << " (expected 33)" << std::endl;
  assert(r3 == 33u);

  // test4: count_odd(1) = 1 + count_even(0) = 1 + 5 = 6.
  auto r4 = MFE::test4;
  std::cout << "test4 = " << r4 << " (expected 6)" << std::endl;
  assert(r4 == 6u);

  std::cout << "All mutual_fix_escape tests passed!" << std::endl;
  return 0;
}
