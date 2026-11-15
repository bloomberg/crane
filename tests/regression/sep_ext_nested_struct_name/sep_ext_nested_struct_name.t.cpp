// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "SepExtNestedStructName.h"
#include <cassert>

int main() {
  // Depth 2, plus one node of NestedLib's tree.
  assert(SepExtNestedStructName::total == 3);
  return 0;
}
