// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// WIP: TODO from src/modutil.ml:365 — empty type args in self-recursive call.
// When optim_se converts Dterm(MLfix) to Dfix, the self-reference becomes
// MLglob(r, []) with no type args. For polymorphic functions where A appears
// only in the return type, C++ can't deduce A from the value arguments.
// Bug status: REPLICATED (C++ compilation fails — template deduction error).

#include "todo_modutil_poly_fix.h"

#include <cassert>

int main() {
  // build_nil_list<nat>(3) should return an empty list (all S cases recurse to O)
  auto r = TodoModutilPolyFix::test_nat;
  (void)r;
  return 0;
}
