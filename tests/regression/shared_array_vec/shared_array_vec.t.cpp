// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <shared_array_vec.h>
#include <cassert>

int main() {
  assert(SharedArrayVec::result == 5 + 100 + 6 + (6 + 6 + 7));
  return 0;
}
