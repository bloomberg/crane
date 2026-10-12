// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <error_failwith.h>
#include <cassert>

int main() {
  assert(ErrorFailwith::result() == 5);
  return 0;
}
