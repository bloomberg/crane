// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <dependent_extraction_targets.h>
#include <dependent_extraction_targets_inner.h>
#include <dependent_extraction_targets_a.h>
#include <dependent_extraction_targets_b.h>
#include <dependent_extraction_targets_rep.h>
#include <cassert>

int main() {
  assert(DependentExtractionTargets::result == 4 + 9 + 3);
  return 0;
}
