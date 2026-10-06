// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <reuse_list_shapes.h>
#include <cassert>

int main() {
  // (1+10 + 2+20 + 3+30) + (5+6) + (2+3) + (7+1) + (4+5) + (9+3).
  assert(ReuseListShapes::result == 66 + 11 + 5 + 8 + 9 + 12);
  return 0;
}
