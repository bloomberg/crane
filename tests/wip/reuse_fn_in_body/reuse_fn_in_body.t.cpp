#include <reuse_fn_in_body.h>

#include <cassert>
#include <iostream>

int main() {
  using R = ReuseFnInBody;

  auto r1 = R::test1;
  std::cout << "test1 = " << r1 << " (expected 12)" << std::endl;
  assert(r1 == 12u);

  auto r2 = R::test2;
  std::cout << "test2 = " << r2 << " (expected 20)" << std::endl;
  assert(r2 == 20u);

  std::cout << "All tests passed!" << std::endl;
  return 0;
}
