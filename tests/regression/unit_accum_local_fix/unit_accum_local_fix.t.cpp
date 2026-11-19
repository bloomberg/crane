// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "unit_accum_local_fix.h"

#include <iostream>

namespace {

int testStatus = 0;

void aSsErT(bool condition, const char *message, int line) {
  if (condition) {
    std::cout << "Error " __FILE__ "(" << line << "): " << message
              << "    (failed)" << std::endl;

    if (0 <= testStatus && testStatus <= 100) {
      ++testStatus;
    }
  }
}

} // namespace

#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

int main() {
  for (uint64_t n = 1; n <= 6; ++n) {
    ASSERT(UnitAccumLocalFix::fill(n) == (n - 1) * 2);
    ASSERT(UnitAccumLocalFix::fill_top(n) == (n - 1) * 3);
  }

  auto l = ListDef::seq(UINT64_C(1), UINT64_C(4));
  UnitAccumLocalFix::walk_top(l);
  UnitAccumLocalFix::walk(l);
  auto p = UnitAccumLocalFix::walk_pair(l);
  ASSERT(p.second == 4);
  auto q = UnitAccumLocalFix::walk_twice(l);
  (void)q;
  ASSERT(UnitAccumLocalFix::sum_with_unit(l) == 1 + 2 + 3 + 4);

  if (testStatus == 0) {
    std::cout << "\nAll unit_accum_local_fix tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
