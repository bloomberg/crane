// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// WIP: TODO from src/mlutil.ml:1304 — iota_red missing cases.
// The iota_red optimization raises Impossible for some complex patterns
// (Prel with multiple vars, Pwild with bound vars). This causes iota
// reduction to be skipped, producing correct but unoptimized code.
// Bug status: DOCUMENTED (passes, but some iota optimizations are skipped).

#include "todo_iota_complex_pattern.h"

#include <cassert>

int main() {
  assert(TodoIotaComplexPattern::test1 == 6u);
  auto t2 = TodoIotaComplexPattern::test2;
  (void)t2;
  return 0;
}
