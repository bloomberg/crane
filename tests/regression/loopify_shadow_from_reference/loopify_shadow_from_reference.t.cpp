// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <loopify_shadow_from_reference.h>

#include <cassert>
#include <cstdio>

int main() {
  using M = LoopifyShadowFromReference;
  // g [3;2;1]: each head x becomes x + 2 * sum of the tail.
  assert(M::suml(M::g(M::upto(UINT64_C(3)))) == 14);
  assert(M::suml(M::g(M::upto(UINT64_C(100)))) > 0);
  std::printf("loopify_shadow_from_reference: ok\n");
  return 0;
}
