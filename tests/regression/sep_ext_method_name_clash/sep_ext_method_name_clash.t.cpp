// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "SepExtMethodNameClash.h"
#include <cassert>

int main() {
  // 1 + 2 + 3, plus 0 for a node and 1 for a leaf.
  assert(SepExtMethodNameClash::total == 7);
  return 0;
}
