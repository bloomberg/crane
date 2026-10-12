// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <conservative_types_kept_parameter.h>
#include <cassert>

int main() {
  assert(ConservativeTypesKeptParameter::mine == 2);
  assert(ConservativeTypesKeptParameter::stdlib == 3);
  return 0;
}
