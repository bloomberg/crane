#include <mutual_lambda_ground_instance.h>
#include <cassert>
#include <cstdint>
#include <iostream>

using M = MutualLambdaGroundInstance;

int main() {
  // run 0 is the list's length; past it f goes on at bool, where the
  // lambda's 10 plus g's one ends an odd n, and dbl 0 an even one.
  assert(M::run(0) == 3);
  for (uint64_t n = 1; n < 32; n++)
    assert(M::run(n) == (n % 2 == 0 ? 0 : 11));
  std::cout << "run 7 = " << M::run(7) << " (want 11)" << std::endl;
  return 0;
}
