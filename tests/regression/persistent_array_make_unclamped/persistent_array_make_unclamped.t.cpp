// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <persistent_array_make_unclamped.h>
#include <cassert>

int main() {
  assert(PersistentArrayMakeUnclamped::len == 4194303);
  return 0;
}
