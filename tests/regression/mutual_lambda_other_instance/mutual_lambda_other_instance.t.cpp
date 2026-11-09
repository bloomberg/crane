#include <mutual_lambda_other_instance.h>
#include <cassert>
#include <cstdint>
#include <iostream>

using M = MutualLambdaOtherInstance;

int main() {
  // run 0 is the list's length; past it the calls go on at bool, ending in
  // the lambda's 10, plus one where g's own zero ends them.
  assert(M::run(0) == 3);
  for (uint64_t n = 1; n < 32; n++)
    assert(M::run(n) == (n % 2 == 0 ? 10 : 11));
  std::cout << "run 7 = " << M::run(7) << " (want 11)" << std::endl;
  return 0;
}
