// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <loopify_method_local_fix.h>

#include <cassert>
#include <cstdio>

int main() {
  using tree = LoopifyMethodLocalFix::Tree::tree;
  // drain (Node (Node Leaf 2) 3) 5 counts 10 down to 0 in [go].
  assert(tree::node(tree::node(tree::leaf(), UINT64_C(2)), UINT64_C(3)).drain(UINT64_C(5)) == 10);
  // Ten million steps of [go]: as a lambda calling itself, the stack overflows.
  assert(tree::leaf().drain(UINT64_C(10000000)) == UINT64_C(10000000));
  std::printf("loopify_method_local_fix: ok\n");
  return 0;
}
