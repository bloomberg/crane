// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <guard_compare_mapped_result.h>
#include <cassert>

int main() {
  assert(GuardCompareMappedResult::same);
  assert(GuardCompareMappedResult::self);
  assert(!GuardCompareMappedResult::differ);
  return 0;
}
