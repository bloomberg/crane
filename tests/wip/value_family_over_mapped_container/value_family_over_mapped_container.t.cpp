// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <value_family_over_mapped_container.h>
#include <cassert>

int main() {
  assert(ValueFamilyOverMappedContainer::from_literal == 7);
  assert(ValueFamilyOverMappedContainer::from_call == 5);
  return 0;
}
