// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <loopify_coerced_recursive_call.h>

#include <cassert>
#include <cstdint>
#include <iostream>

using M = LoopifyCoercedRecursiveCall;

#ifndef DEPTH
#define DEPTH 100000
#endif

int main() {
  assert(M::run == 4);
  // A succE chain deep enough that a C++ call of eval per level would
  // exhaust the stack.  It is never destroyed: expr, an indexed family, has
  // no iterative destructor (wip/indexed_family_deep_destructor), and
  // tearing the chain down would overflow the stack as well.
  M::expr *e = new M::expr(M::expr::lit(0));
  for (int i = 0; i < DEPTH; ++i) {
    *e = M::expr::succe(std::move(*e));
  }
  assert(crane::any_cast<uint64_t>(M::eval<uint64_t>(*e)) == DEPTH);
  std::cout << "loopify_coerced_recursive_call: ok\n";
  return 0;
}
