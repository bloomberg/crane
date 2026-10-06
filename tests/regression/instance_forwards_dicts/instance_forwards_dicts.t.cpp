// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <instance_forwards_dicts.h>
#include <cassert>

int main() {
  // Neg 2 (EMeta (MExp (Lit B 12))): 2 + 100 + 12.
  assert(InstanceForwardsDicts::result == 114);
  return 0;
}
