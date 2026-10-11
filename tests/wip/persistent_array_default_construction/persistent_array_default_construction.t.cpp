// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <persistent_array_default_construction.h>
#include <cassert>

int main() {
  assert(PersistentArrayDefaultConstruction::centre == 5);
  assert(PersistentArrayDefaultConstruction::first == 7);
  return 0;
}
