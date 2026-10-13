// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <dependent_extraction_targets.h>
#include <cassert>

int main() {
  assert(DependentExtractionTargets::result == 4 + 9 + 3);
  return 0;
}
