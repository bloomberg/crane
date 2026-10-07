// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <shared_variant_nested.h>
#include <cassert>

int main() {
  // rsum r0 = 10, rsum r1 = 14, clen c0 = 3, ssize s0 = 5,
  // and the shapes' volumes 24 + 0 + 1.
  assert(SharedVariantNested::result == 10 + 14 + 3 + 5 + 25);
  // [r1] was built from [r0] without changing it.
  assert(SharedVariantNested::r0.rsum() == 10);
  return 0;
}
