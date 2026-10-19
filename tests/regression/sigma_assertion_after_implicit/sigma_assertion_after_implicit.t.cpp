// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <sigma_assertion_after_implicit.h>
#include <cassert>

int main() {
  assert(SigmaAssertionAfterImplicit::test == 8);
  return 0;
}
