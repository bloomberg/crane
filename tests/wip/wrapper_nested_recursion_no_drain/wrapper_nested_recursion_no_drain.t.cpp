#include "wrapper_nested_recursion_no_drain.h"
#include <cassert>
#include <cstdint>
#include <iostream>

// A [rose] this deep is a chain of 60000 heap cells. Building it is
// loopified and so costs no C++ call stack; tearing it down recurses once
// per cell through the default member-wise destructor and overflows.
int main() {
  auto r = WrapperNestedRecursionNoDrain::test_deep(UINT64_C(60000));
  std::cout << "test_deep(60000) = " << r << std::endl;
  assert(r == 0);
  std::cout << "ok" << std::endl;
  return 0;
}
