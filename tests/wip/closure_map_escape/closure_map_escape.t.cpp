#include <closure_map_escape.h>

#include <cassert>
#include <iostream>

int main() {
  using CME = ClosureMapEscape;

  // test1: map_to_adders [10,20,30], apply first to 5.
  // BUG: each fixpoint captures pattern variable h by [&].
  // Expected: 10 + 5 = 15.
  auto r1 = CME::test1;
  std::cout << "test1 = " << r1 << " (expected 15)" << std::endl;
  assert(r1 == 15u);

  // test2: sum of applying all adders to 0.
  // Expected: 10 + 20 + 30 = 60.
  auto r2 = CME::test2;
  std::cout << "test2 = " << r2 << " (expected 60)" << std::endl;
  assert(r2 == 60u);

  // test3: noise between closure creation and use.
  // Expected: (1+100) + (1+200) = 302.
  auto r3 = CME::test3;
  std::cout << "test3 = " << r3 << " (expected 302)" << std::endl;
  assert(r3 == 302u);

  std::cout << "All closure_map_escape tests passed!" << std::endl;
  return 0;
}
