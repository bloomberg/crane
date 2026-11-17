#include <local_mutual_partner_type_arg.h>
#include <cassert>
#include <cstdint>
#include <iostream>

using M = LocalMutualPartnerTypeArg;

int main() {
  // f 0 = k; f (n+1) = g (+k) n n, which is n + k at 0 and f (n-1) + 1 past it.
  const uint64_t want[] = {1, 1, 2, 2, 3, 3};
  for (uint64_t n = 0; n < 6; n++)
    assert(M::run(1, n) == want[n]);
  std::cout << "run 1 5 = " << M::run(1, 5) << " (want 3)" << std::endl;
  return 0;
}
