// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <loopify_nested_local_fix.h>

#include <cassert>
#include <cstdio>

int main() {
  using M = LoopifyNestedLocalFix;
  assert(M::count(List<uint64_t>::cons(UINT64_C(2), List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()))) == 5);
  // Ten million steps of [inner]: as a lambda calling itself, the stack overflows.
  assert(M::count(List<uint64_t>::cons(UINT64_C(10000000), List<uint64_t>::nil())) == UINT64_C(10000000));
  std::printf("loopify_nested_local_fix: ok\n");
  return 0;
}
