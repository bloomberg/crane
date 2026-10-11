// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <loopify_owned_child_pointer.h>
#include <cassert>

int main() {
  assert(LoopifyOwnedChildPointer::size == 9);
  assert(LoopifyOwnedChildPointer::left_sums == 4);
  return 0;
}
