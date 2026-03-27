// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_scans.h>

namespace {
int testStatus = 0;
void aSsErT(bool condition, const char *message, int line) {
  if (condition) {
    std::cout << "Error " __FILE__ "(" << line << "): " << message
              << "    (failed)" << std::endl;
    if (0 <= testStatus && testStatus <= 100)
      ++testStatus;
  }
}
} // namespace
#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

using UIntList = List<unsigned int>;

int main() {
  auto nil = UIntList::nil();
  auto l5 = UIntList::cons(1u, UIntList::cons(2u, UIntList::cons(
    3u, UIntList::cons(4u, UIntList::cons(5u, nil)))));

  // scanl
  auto scanned = LoopifyScans::scanl(0u, l5);
  ASSERT(scanned != nullptr);

  // scanl_mult
  auto scanned_mult = LoopifyScans::scanl_mult(1u, l5);
  ASSERT(scanned_mult != nullptr);

  // running_max
  auto rmax = LoopifyScans::running_max(0u, l5);
  ASSERT(rmax != nullptr);

  // running_min
  auto rmin = LoopifyScans::running_min(100u, l5);
  ASSERT(rmin != nullptr);

  // pairwise_diff
  auto pdiff = LoopifyScans::pairwise_diff(0u, l5);
  ASSERT(pdiff != nullptr);

  // accumulate_if_even
  auto acc_even = LoopifyScans::accumulate_if_even(0u, l5);
  ASSERT(acc_even != nullptr);

  if (testStatus > 0) {
    std::cerr << "Error: " << testStatus << " test(s) failed." << std::endl;
    return testStatus;
  }
  return 0;
}
