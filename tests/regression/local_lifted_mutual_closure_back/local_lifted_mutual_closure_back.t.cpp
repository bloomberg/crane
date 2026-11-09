#include <local_lifted_mutual_closure_back.h>
#include <cassert>
#include <cstdint>
#include <iostream>

using M = LocalLiftedMutualClosureBack;

int main() {
  // At the list (h y = 3) plus at bool (h y = 1): each step of f into g
  // adds one to the callable; g's own zero adds k.
  const uint64_t want[] = {4, 8, 6, 10, 8, 12};
  for (uint64_t n = 0; n < 6; n++)
    assert(M::run(1, n) == want[n]);
  std::cout << "run 1 5 = " << M::run(1, 5) << " (want 12)" << std::endl;
  return 0;
}
