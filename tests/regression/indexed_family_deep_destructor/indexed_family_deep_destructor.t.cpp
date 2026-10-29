// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
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
