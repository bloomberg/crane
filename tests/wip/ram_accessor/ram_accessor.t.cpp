// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <cassert>
#include <ram_accessor.h>
int main() {
  assert(RamAccessor::init_read == 0u);
  assert(RamAccessor::ram_read_main(RamAccessor::init_state) == 0u);
  return 0;
}
