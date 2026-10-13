// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <family_with_type_binder_at_function.h>
#include <cassert>

int main() {
  assert(FamilyWithTypeBinderAtFunction::result == 2 + 5 + 3);
  return 0;
}
