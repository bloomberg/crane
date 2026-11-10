#include <local_fix_polymorphic_recursion.h>
#include <cassert>
#include <cstdint>
#include <iostream>

using M = LocalFixPolymorphicRecursion;

int main() {
  // run k 0 is the list's length; past it the lambda's 10 + k.
  assert(M::run(1, 0) == 3);
  for (uint64_t n = 1; n < 6; n++)
    assert(M::run(1, n) == 11);
  std::cout << "run 1 5 = " << M::run(1, 5) << " (want 11)" << std::endl;
  return 0;
}
