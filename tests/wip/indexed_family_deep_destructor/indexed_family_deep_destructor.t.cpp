// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Expected: SEGFAULT (stack overflow) destroying a deep chain of expr, an
// indexed family, which has no iterative destructor.
// When fixed: prints "indexed_family_deep_destructor: ok".
#include <indexed_family_deep_destructor.h>

#include <iostream>

using M = IndexedFamilyDeepDestructor;

#ifndef DEPTH
#define DEPTH 100000
#endif

int main() {
  {
    M::expr e = M::expr::lit(0);
    for (int i = 0; i < DEPTH; ++i) {
      e = M::expr::succe(std::move(e));
    }
  }
  std::cout << "indexed_family_deep_destructor: ok\n";
  return 0;
}
