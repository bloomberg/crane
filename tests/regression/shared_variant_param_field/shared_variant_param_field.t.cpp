// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <shared_variant_param_field.h>
#include <cassert>

int main() {
  // (1+2) + (3+4) + (5+6+7), twice.
  assert(SharedVariantParamField::result == 2 * (3 + 7 + 18));
  return 0;
}
