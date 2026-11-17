#include <local_lifted_mutual.h>
#include <cassert>
#include <cstdint>
#include <iostream>

using M = LocalLiftedMutual;

int main() {
  // At the list (h y = 3) plus at bool (h y = 1): f n is h y at 0 and
  // g (n-1) + 1 past it; g n is h y + k at 0 and f (n-1) past it.
  const uint64_t want[] = {4, 8, 6, 10, 8, 12};
  for (uint64_t n = 0; n < 6; n++)
    assert(M::run(1, n) == want[n]);
  std::cout << "run 1 5 = " << M::run(1, 5) << " (want 12)" << std::endl;
  return 0;
}
