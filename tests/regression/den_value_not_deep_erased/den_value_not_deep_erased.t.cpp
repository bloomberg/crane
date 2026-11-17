// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <den_value_not_deep_erased.h>
#include <cassert>

int main() {
  assert(DenValueNotDeepErased::from_call == 6);
  assert(DenValueNotDeepErased::from_nested == 6);
  return 0;
}
