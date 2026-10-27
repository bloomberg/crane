// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <loopify_receiver_from_temporary.h>

#include <cassert>
#include <iostream>

using M = LoopifyReceiverFromTemporary;

int main() {
  assert(M::go(0) == 0);
  assert(M::go(1) == 1);
  assert(M::go(5) == 5);
  // Deep enough that the recursion the loop replaced would exhaust the stack.
  assert(M::go(200000) == 200000);
  std::cout << "loopify_receiver_from_temporary: ok\n";
  return 0;
}
