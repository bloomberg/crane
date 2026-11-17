// A global Core reaches unapplied and translation applies: the call it builds
// is elaborated where it is translated.
#include "eta_extended_global_elaborated.h"

#include <cassert>
#include <iostream>

int main() {
  using M = EtaExtendedGlobalElaborated;
  List<uint64_t> l = List<uint64_t>::nil();
  for (uint64_t i = 7; i > 0; --i) l = List<uint64_t>::cons(i, l);
  assert(M::count_odds(l) == 4);
  assert(M::count_evens(l) == 3);
  assert(M::count_odds(List<uint64_t>::nil()) == 0);
  std::cout << "eta_extended_global_elaborated: count_odds(1..7)=" << M::count_odds(l) << " PASSED" << std::endl;
  return 0;
}
