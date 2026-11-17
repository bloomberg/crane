// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <record_destructure_once_expr.h>

#include <cassert>
#include <iostream>

int main() {
  using M = RecordDestructureOnceExpr;

  std::cout << "steps = " << M::r_steps << std::endl;
  assert(M::r_steps == 40u);

  std::cout << "All record_destructure_once_expr tests passed!" << std::endl;
  return 0;
}
