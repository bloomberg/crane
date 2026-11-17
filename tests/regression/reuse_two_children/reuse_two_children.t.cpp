// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <reuse_two_children.h>
#include <cassert>

int main() {
  // 33 + 88 + 50 + 5 nodes.
  assert(ReuseTwoChildren::result == 176);
  return 0;
}
