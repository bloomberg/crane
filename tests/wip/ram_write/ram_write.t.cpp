// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <cassert>
#include <ram_write.h>
int main() {
  assert(RamWrite::write_bank_count == 4u);
  return 0;
}
