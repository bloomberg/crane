// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <loopify_moves_captured_closure.h>
#include <cassert>

int main() {
  assert(LoopifyMovesCapturedClosure::in_tree == 6);
  assert(LoopifyMovesCapturedClosure::in_list == 12);
  assert(LoopifyMovesCapturedClosure::in_acc == 9);
  return 0;
}
