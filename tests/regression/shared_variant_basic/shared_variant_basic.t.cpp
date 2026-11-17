// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <shared_variant_basic.h>
#include <cassert>

int main() {
  // find 4 t0 = 40, find 4 t1 = 44, find 9 t1 = 90, sizes 7 and 7.
  assert(SharedVariantBasic::tree_result == 40 + 44 + 90 + 7 + 7);
  assert(SharedVariantBasic::list_result == 2 + 3 + 4);
  // A long list built, measured and dropped.
  assert(SharedVariantBasic::long_result(1000000) == 1000000);
  return 0;
}
