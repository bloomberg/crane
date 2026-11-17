// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <par_future_read_twice.h>
#include <cassert>

int main() {
  assert(ParFutureReadTwice::twice(4) == 32);
  assert(ParFutureReadTwice::listed == 14);
  return 0;
}
