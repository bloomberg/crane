// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <single_threaded_heap.h>
#include <cassert>

#ifndef CRANE_SINGLE_THREADED
#error "Set Crane SingleThreaded did not reach the generated header"
#endif

int main() {
  // 200 nodes, plus 5 + 1000.
  assert(SingleThreadedHeap::result == 200 + 5 + 1000);
  return 0;
}
