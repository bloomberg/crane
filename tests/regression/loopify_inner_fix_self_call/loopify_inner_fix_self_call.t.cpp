// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <loopify_inner_fix_self_call.h>

#include <cassert>
#include <cstdint>
#include <iostream>

using M = LoopifyInnerFixSelfCall;

int main() {
  M::tree l = M::tree::node(M::tree::leaf(), 5, M::tree::leaf());
  M::tree r = M::tree::node(
      M::tree::node(M::tree::node(M::tree::leaf(), 1, M::tree::leaf()), 2,
                    M::tree::leaf()),
      3, M::tree::leaf());
  M::tree j = M::join(l, 4, r);
  assert(M::size(j) == M::size(l) + M::size(r) + 1);
  assert(M::size(M::join(M::tree::leaf(), 0, r)) == M::size(r) + 1);
  std::cout << "loopify_inner_fix_self_call: ok\n";
  return 0;
}
