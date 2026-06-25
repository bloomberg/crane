// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// WIP: TODO from src/mlutil.ml:221 — generalizable approximation for C++.
// The `generalizable` function uses an approximation: for C++, only MLapp
// is non-generalizable. This test checks let-binding behavior.
// Bug status: DOCUMENTED (passes, but the approximation is imprecise).

#include "todo_generalizable_approx.h"

#include <cassert>

int main() {
  assert(TodoGeneralizableApprox::test1 == 7u);   // f(f(5)) = f(6) = 7
  assert(TodoGeneralizableApprox::test2 == 7u);   // (3+3)+1 = 7
  return 0;
}
