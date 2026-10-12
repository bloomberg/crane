// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <extraction_implicit_call_sites.h>
#include <cassert>

int main() {
  assert(ExtractionImplicitCallSites::counted == 3);
  assert(ExtractionImplicitCallSites::walked == 4);
  return 0;
}
