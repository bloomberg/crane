// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <par_unit_not_concurrent.h>
#include <cassert>

int main() {
  for (int i = 0; i < 20; ++i)
    assert(ParUnitNotConcurrent::race(40) == 4 * (2000 * 2001 / 2 + 3000 * 3001 / 2));
  return 0;
}
