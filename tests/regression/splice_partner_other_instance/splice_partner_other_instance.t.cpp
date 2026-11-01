#include <splice_partner_other_instance.h>
#include <cassert>
#include <cstdint>
#include <iostream>

using M = SplicePartnerOtherInstance;

int main() {
  // run 0 is the list's length; past it the calls go on at bool, ending in
  // weight true, plus one where g's own zero ends them.
  assert(M::run(0) == 3);
  assert(M::run(1) == 11);
  assert(M::run(2) == 10);
  assert(M::run(3) == 11);
  for (uint64_t n = 4; n < 64; n++)
    assert(M::run(n) == (n % 2 == 0 ? 10 : 11));
  std::cout << "run 7 = " << M::run(7) << " (want 11)" << std::endl;
  return 0;
}
