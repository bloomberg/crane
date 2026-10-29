// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <loopify_existential_recursive_call.h>

#include <cassert>
#include <cstdint>
#include <iostream>

using M = LoopifyExistentialRecursiveCall;

#ifndef DEPTH
#define DEPTH 100000
#endif

int main() {
  assert(M::run == 4);
  // fstE (pairE (fstE (pairE ... (lit 0) ...) (bl true))) (bl true)),
  // DEPTH levels, torn down by expr's iterative destructor.
  M::expr e = M::expr::lit(0);
  for (int i = 0; i < DEPTH; ++i) {
    e = M::expr::fste(M::expr::paire(std::move(e), M::expr::bl(true)));
  }
#ifndef BUILD_ONLY
  assert(crane::any_cast<uint64_t>(M::eval<uint64_t>(e)) == 0);
#endif
  std::cout << "loopify_existential_recursive_call: ok\n";
  return 0;
}
