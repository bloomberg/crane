#include <closure_let_escape.h>

#include <cassert>
#include <iostream>

int main() {
  using CLE = ClosureLetEscape;

  // test1: make_fn_fix(21) => base=42, add(3) = 42+3 = 45.
  // BUG: fixpoint captures let-binding base by [&], dangles.
  auto r1 = CLE::test1;
  std::cout << "test1 = " << r1 << " (expected 45)" << std::endl;
  assert(r1 == 45u);

  // test2: make_fn_fix(50) => base=100, add(15) = 100+15 = 115.
  auto r2 = CLE::test2;
  std::cout << "test2 = " << r2 << " (expected 115)" << std::endl;
  assert(r2 == 115u);

  // test3: make_fn_multi(10) => a=11, b=33, helper(5) = (11+33)+5 = 49.
  auto r3 = CLE::test3;
  std::cout << "test3 = " << r3 << " (expected 49)" << std::endl;
  assert(r3 == 49u);

  std::cout << "All closure_let_escape tests passed!" << std::endl;
  return 0;
}
