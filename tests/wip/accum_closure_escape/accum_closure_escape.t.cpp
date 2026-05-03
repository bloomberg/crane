#include <accum_closure_escape.h>

#include <cassert>
#include <iostream>

int main() {
  using ACE = AccumClosureEscape;

  auto r1 = ACE::test1;
  std::cout << "test1 = " << r1 << " (expected 35)" << std::endl;
  assert(r1 == 35u);

  auto r2 = ACE::test2;
  std::cout << "test2 = " << r2 << " (expected 75)" << std::endl;
  assert(r2 == 75u);

  auto r3 = ACE::test3;
  std::cout << "test3 = " << r3 << " (expected 67)" << std::endl;
  assert(r3 == 67u);

  auto r4 = ACE::test4;
  std::cout << "test4 = " << r4 << " (expected 75)" << std::endl;
  assert(r4 == 75u);

  auto r5 = ACE::test5;
  std::cout << "test5 = " << r5 << " (expected 100)" << std::endl;
  assert(r5 == 100u);

  std::cout << "All accum_closure_escape tests passed!" << std::endl;
  return 0;
}
