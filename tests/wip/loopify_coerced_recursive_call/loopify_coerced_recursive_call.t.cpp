// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Expected: SEGFAULT (stack overflow) in eval, whose machine leaves the
// coerced recursive call of each succE as a C++ call.
// When fixed: prints "loopify_coerced_recursive_call: ok".
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
  // A succE chain deep enough that a C++ call of eval per level exhausts the
  // stack.  It is never destroyed: expr, an indexed family, has no iterative
  // destructor, and tearing the chain down would overflow the stack as
  // well, hiding what this test is about.
  M::expr *e = new M::expr(M::expr::lit(0));
  for (int i = 0; i < DEPTH; ++i) {
    *e = M::expr::succe(std::move(*e));
  }
#ifndef BUILD_ONLY
  assert(crane::any_cast<uint64_t>(M::eval<uint64_t>(*e)) == DEPTH);
#endif
  std::cout << "loopify_coerced_recursive_call: ok\n";
  return 0;
}
