// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <callable_crossing_matrix.h>
#include <cassert>

using M = CallableCrossingMatrix;

int main() {
  // Seven sources of [1 + 2] in each slot.
  for (auto n : {M::r2_param, M::r2_tvar, M::r2_auto, M::r2_loop, M::r2_return, M::r2_let,
                 M::r2_field, M::r2_erased}) {
    assert(n == 7 * 3);
  }
  // Four sources of [1 + 2 + 3] in each slot.
  for (auto n : {M::r3_param, M::r3_tvar, M::r3_auto, M::r3_loop, M::r3_return, M::r3_let,
                 M::r3_field}) {
    assert(n == 4 * 6);
  }
  return 0;
}
