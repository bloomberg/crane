// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <cassert>
#include <page_address.h>
int main() {
  assert(PageAddress::page_base_777 == 768u);
  assert(PageAddress::page_base(0u) == 0u);
  assert(PageAddress::page_of(777u) == 3u);
  assert(PageAddress::branch_example == PageAddress::branch_target(100u, 42u));
  return 0;
}
