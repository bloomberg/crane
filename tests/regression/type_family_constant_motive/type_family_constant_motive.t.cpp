// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <type_family_constant_motive.h>
#include <cassert>

int main() {
  assert(TypeFamilyConstantMotive::first);
  assert(TypeFamilyConstantMotive::max_is_left);
  return 0;
}
