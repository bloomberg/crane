#include <double_invoke_move.h>

#include <cassert>
#include <iostream>

int main() {
  using DIM = DoubleInvokeMove;

  // wrap_with t creates a closure. If std::move(t) is inside the lambda
  // body and the closure is called twice, the second call gets a null t.
  // Expected: 20 + 20 = 40
  auto r = DIM::bug_double_invoke;
  std::cout << "bug_double_invoke = " << r << std::endl;
  assert(r == 40u);

  std::cout << "All double_invoke_move tests passed!" << std::endl;
  return 0;
}
