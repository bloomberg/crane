// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <guard_compare_shared.h>
#include <cassert>
#include <chrono>

using M = GuardCompareShared;

int main() {
  auto a = M::build(2000), b = M::build(2000), c = M::build(1999);
  // Structurally equal but separate trees are compared all the way down.
  assert(M::tcompare(a, b) == Comparison::EQ);
  assert(M::tcompare(c, a) == Comparison::LT);
  assert(M::tcompare(a, c) == Comparison::GT);
  // A copy of a tree's handle is another object holding the same block: the
  // guard sees one value and answers at once.  A million full walks of 2000
  // nodes would take minutes.
  auto a2 = a;
  auto start = std::chrono::steady_clock::now();
  for (int i = 0; i < 1000000; ++i) assert(M::tcompare(a, a2) == Comparison::EQ);
  auto ms = std::chrono::duration_cast<std::chrono::milliseconds>(
      std::chrono::steady_clock::now() - start).count();
  assert(ms < 5000);
  return 0;
}
