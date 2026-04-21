#include <fix_curried_escape.h>

#include <cassert>
#include <iostream>

int main() {
  using FCE = FixCurriedEscape;

  auto r1 = FCE::test1;
  std::cout << "test1 = " << r1 << " (expected 45)" << std::endl;
  assert(r1 == 45u);

  auto r2 = FCE::test2;
  std::cout << "test2 = " << r2 << " (expected 17)" << std::endl;
  assert(r2 == 17u);

  auto r3 = FCE::test3;
  std::cout << "test3 = " << r3 << " (expected 105)" << std::endl;
  assert(r3 == 105u);

  std::cout << "All tests passed!" << std::endl;
  return 0;
}
