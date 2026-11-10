#include <local_mutual_polymorphic_recursion.h>
#include <cassert>
#include <cstdint>
#include <iostream>

using M = LocalMutualPolymorphicRecursion;

int main() {
  // As mutual_lambda_other_instance: the list's length at 0, past it the
  // lambda's 10, plus one where g's own zero ends the calls.
  assert(M::run(0) == 3);
  for (uint64_t n = 1; n < 32; n++)
    assert(M::run(n) == (n % 2 == 0 ? 10 : 11));
  std::cout << "run 7 = " << M::run(7) << " (want 11)" << std::endl;
  return 0;
}
