// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <n_to_nat_representation.h>
#include <cassert>

int main() {
  assert(NToNatRepresentation::larger == 300);
  assert(NToNatRepresentation::smaller == 7);
  assert(NToNatRepresentation::big == 5000000000ULL);
  return 0;
}
