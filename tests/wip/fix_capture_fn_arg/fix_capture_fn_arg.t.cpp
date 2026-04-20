#include <fix_capture_fn_arg.h>

#include <cassert>
#include <iostream>

int main() {
  using FCA = FixCaptureFnArg;

  // test1: make_transform(x=>x*2, 5) => (10, go). 10 + go(3) = 10 + 13 = 23.
  // BUG: go captures f (std::function) and base by [&].
  auto r1 = FCA::test1;
  std::cout << "test1 = " << r1 << " (expected 23)" << std::endl;
  assert(r1 == 23u);

  // test2: make_transform(S, 10) => (11, go). 11 + go(5) = 11 + 16 = 27.
  auto r2 = FCA::test2;
  std::cout << "test2 = " << r2 << " (expected 27)" << std::endl;
  assert(r2 == 27u);

  std::cout << "All fix_capture_fn_arg tests passed!" << std::endl;
  return 0;
}
