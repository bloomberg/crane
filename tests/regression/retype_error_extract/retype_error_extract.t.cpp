// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// Regression: extraction must not crash with Retyping.RetypeError
// when a type-scheme definition has a lambda body.

#include "RetypeErrorExtract.h"

#include <cassert>

int main() {
  assert(RetypeErrorExtract::value == 42u);
  return 0;
}
